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
lean_object* v___f_720_; lean_object* v___x_721_; 
v___f_720_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0));
v___x_721_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_712_, v_inst_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___x_729_; uint8_t v___x_730_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
v___x_723_ = lean_array_get_size(v_a_722_);
v___x_729_ = lean_unsigned_to_nat(0u);
v___x_730_ = lean_nat_dec_eq(v___x_723_, v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___y_734_; uint8_t v___x_736_; 
lean_dec_ref_known(v___x_721_, 1);
v___x_731_ = lean_unsigned_to_nat(1u);
v___x_732_ = lean_nat_sub(v___x_723_, v___x_731_);
v___x_736_ = lean_nat_dec_le(v___x_729_, v___x_732_);
if (v___x_736_ == 0)
{
lean_inc(v___x_732_);
v___y_734_ = v___x_732_;
goto v___jp_733_;
}
else
{
v___y_734_ = v___x_729_;
goto v___jp_733_;
}
v___jp_733_:
{
uint8_t v___x_735_; 
v___x_735_ = lean_nat_dec_le(v___y_734_, v___x_732_);
if (v___x_735_ == 0)
{
lean_dec(v___x_732_);
lean_inc(v___y_734_);
v___y_725_ = v___y_734_;
v___y_726_ = v___y_734_;
goto v___jp_724_;
}
else
{
v___y_725_ = v___y_734_;
v___y_726_ = v___x_732_;
goto v___jp_724_;
}
}
}
else
{
lean_dec(v_a_722_);
return v___x_721_;
}
v___jp_724_:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_720_, v___x_723_, v_a_722_, v___y_725_, v___y_726_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_726_);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
}
else
{
return v___x_721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___boxed(lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg(v_inst_737_, v_inst_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted(lean_object* v_00_u03b1_746_, lean_object* v_inst_747_, lean_object* v_inst_748_, lean_object* v_inst_749_, lean_object* v_inst_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v___f_757_; lean_object* v___x_758_; 
v___f_757_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0));
v___x_758_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_748_, v_inst_749_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_760_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___x_766_; uint8_t v___x_767_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
v___x_760_ = lean_array_get_size(v_a_759_);
v___x_766_ = lean_unsigned_to_nat(0u);
v___x_767_ = lean_nat_dec_eq(v___x_760_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___y_771_; uint8_t v___x_773_; 
lean_dec_ref_known(v___x_758_, 1);
v___x_768_ = lean_unsigned_to_nat(1u);
v___x_769_ = lean_nat_sub(v___x_760_, v___x_768_);
v___x_773_ = lean_nat_dec_le(v___x_766_, v___x_769_);
if (v___x_773_ == 0)
{
lean_inc(v___x_769_);
v___y_771_ = v___x_769_;
goto v___jp_770_;
}
else
{
v___y_771_ = v___x_766_;
goto v___jp_770_;
}
v___jp_770_:
{
uint8_t v___x_772_; 
v___x_772_ = lean_nat_dec_le(v___y_771_, v___x_769_);
if (v___x_772_ == 0)
{
lean_dec(v___x_769_);
lean_inc(v___y_771_);
v___y_762_ = v___y_771_;
v___y_763_ = v___y_771_;
goto v___jp_761_;
}
else
{
v___y_762_ = v___y_771_;
v___y_763_ = v___x_769_;
goto v___jp_761_;
}
}
}
else
{
lean_dec(v_a_759_);
return v___x_758_;
}
v___jp_761_:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_757_, v___x_760_, v_a_759_, v___y_762_, v___y_763_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_763_);
v___x_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
}
else
{
return v___x_758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___boxed(lean_object* v_00_u03b1_774_, lean_object* v_inst_775_, lean_object* v_inst_776_, lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted(v_00_u03b1_774_, v_inst_775_, v_inst_776_, v_inst_777_, v_inst_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
lean_dec(v_inst_778_);
lean_dec_ref(v_inst_775_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(uint8_t v_pu_786_, lean_object* v_c_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
switch(lean_obj_tag(v_c_787_))
{
case 0:
{
lean_object* v_decl_794_; lean_object* v_k_795_; lean_object* v___x_796_; lean_object* v_value_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_decl_794_ = lean_ctor_get(v_c_787_, 0);
lean_inc_ref(v_decl_794_);
v_k_795_ = lean_ctor_get(v_c_787_, 1);
lean_inc_ref(v_k_795_);
lean_dec_ref_known(v_c_787_, 2);
v___x_796_ = lean_st_ref_take(v_a_788_);
v_value_797_ = lean_ctor_get(v_decl_794_, 3);
lean_inc(v_value_797_);
lean_dec_ref(v_decl_794_);
v___x_798_ = lean_array_push(v___x_796_, v_value_797_);
v___x_799_ = lean_st_ref_put(v_a_788_, v___x_798_);
v_c_787_ = v_k_795_;
goto _start;
}
case 1:
{
lean_object* v_decl_801_; lean_object* v_k_802_; lean_object* v_value_803_; lean_object* v___x_804_; 
v_decl_801_ = lean_ctor_get(v_c_787_, 0);
lean_inc_ref(v_decl_801_);
v_k_802_ = lean_ctor_get(v_c_787_, 1);
lean_inc_ref(v_k_802_);
lean_dec_ref_known(v_c_787_, 2);
v_value_803_ = lean_ctor_get(v_decl_801_, 4);
lean_inc_ref(v_value_803_);
lean_dec_ref(v_decl_801_);
v___x_804_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_786_, v_value_803_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_dec_ref_known(v___x_804_, 1);
v_c_787_ = v_k_802_;
goto _start;
}
else
{
lean_dec_ref(v_k_802_);
return v___x_804_;
}
}
case 2:
{
lean_object* v_decl_806_; lean_object* v_k_807_; lean_object* v_value_808_; lean_object* v___x_809_; 
v_decl_806_ = lean_ctor_get(v_c_787_, 0);
lean_inc_ref(v_decl_806_);
v_k_807_ = lean_ctor_get(v_c_787_, 1);
lean_inc_ref(v_k_807_);
lean_dec_ref_known(v_c_787_, 2);
v_value_808_ = lean_ctor_get(v_decl_806_, 4);
lean_inc_ref(v_value_808_);
lean_dec_ref(v_decl_806_);
v___x_809_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_786_, v_value_808_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_dec_ref_known(v___x_809_, 1);
v_c_787_ = v_k_807_;
goto _start;
}
else
{
lean_dec_ref(v_k_807_);
return v___x_809_;
}
}
case 4:
{
lean_object* v_cases_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_833_; 
v_cases_811_ = lean_ctor_get(v_c_787_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v_c_787_);
if (v_isSharedCheck_833_ == 0)
{
v___x_813_ = v_c_787_;
v_isShared_814_ = v_isSharedCheck_833_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_cases_811_);
lean_dec(v_c_787_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_833_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v_alts_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v_alts_815_ = lean_ctor_get(v_cases_811_, 3);
lean_inc_ref(v_alts_815_);
lean_dec_ref(v_cases_811_);
v___x_816_ = lean_unsigned_to_nat(0u);
v___x_817_ = lean_array_get_size(v_alts_815_);
v___x_818_ = lean_box(0);
v___x_819_ = lean_nat_dec_lt(v___x_816_, v___x_817_);
if (v___x_819_ == 0)
{
lean_object* v___x_821_; 
lean_dec_ref(v_alts_815_);
if (v_isShared_814_ == 0)
{
lean_ctor_set_tag(v___x_813_, 0);
lean_ctor_set(v___x_813_, 0, v___x_818_);
v___x_821_ = v___x_813_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_818_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
else
{
uint8_t v___x_823_; 
v___x_823_ = lean_nat_dec_le(v___x_817_, v___x_817_);
if (v___x_823_ == 0)
{
if (v___x_819_ == 0)
{
lean_object* v___x_825_; 
lean_dec_ref(v_alts_815_);
if (v_isShared_814_ == 0)
{
lean_ctor_set_tag(v___x_813_, 0);
lean_ctor_set(v___x_813_, 0, v___x_818_);
v___x_825_ = v___x_813_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_818_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
else
{
size_t v___x_827_; size_t v___x_828_; lean_object* v___x_829_; 
lean_del_object(v___x_813_);
v___x_827_ = ((size_t)0ULL);
v___x_828_ = lean_usize_of_nat(v___x_817_);
v___x_829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_786_, v_alts_815_, v___x_827_, v___x_828_, v___x_818_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
lean_dec_ref(v_alts_815_);
return v___x_829_;
}
}
else
{
size_t v___x_830_; size_t v___x_831_; lean_object* v___x_832_; 
lean_del_object(v___x_813_);
v___x_830_ = ((size_t)0ULL);
v___x_831_ = lean_usize_of_nat(v___x_817_);
v___x_832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_786_, v_alts_815_, v___x_830_, v___x_831_, v___x_818_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
lean_dec_ref(v_alts_815_);
return v___x_832_;
}
}
}
}
case 7:
{
lean_object* v_k_834_; 
v_k_834_ = lean_ctor_get(v_c_787_, 3);
lean_inc_ref(v_k_834_);
lean_dec_ref_known(v_c_787_, 4);
v_c_787_ = v_k_834_;
goto _start;
}
case 8:
{
lean_object* v_k_836_; 
v_k_836_ = lean_ctor_get(v_c_787_, 3);
lean_inc_ref(v_k_836_);
lean_dec_ref_known(v_c_787_, 4);
v_c_787_ = v_k_836_;
goto _start;
}
case 9:
{
lean_object* v_k_838_; 
v_k_838_ = lean_ctor_get(v_c_787_, 5);
lean_inc_ref(v_k_838_);
lean_dec_ref_known(v_c_787_, 6);
v_c_787_ = v_k_838_;
goto _start;
}
case 10:
{
lean_object* v_k_840_; 
v_k_840_ = lean_ctor_get(v_c_787_, 2);
lean_inc_ref(v_k_840_);
lean_dec_ref_known(v_c_787_, 3);
v_c_787_ = v_k_840_;
goto _start;
}
case 11:
{
lean_object* v_k_842_; 
v_k_842_ = lean_ctor_get(v_c_787_, 2);
lean_inc_ref(v_k_842_);
lean_dec_ref_known(v_c_787_, 3);
v_c_787_ = v_k_842_;
goto _start;
}
case 12:
{
lean_object* v_k_844_; 
v_k_844_ = lean_ctor_get(v_c_787_, 3);
lean_inc_ref(v_k_844_);
lean_dec_ref_known(v_c_787_, 4);
v_c_787_ = v_k_844_;
goto _start;
}
case 13:
{
lean_object* v_k_846_; 
v_k_846_ = lean_ctor_get(v_c_787_, 1);
lean_inc_ref(v_k_846_);
lean_dec_ref_known(v_c_787_, 2);
v_c_787_ = v_k_846_;
goto _start;
}
default: 
{
lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec_ref(v_c_787_);
v___x_848_ = lean_box(0);
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
return v___x_849_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(uint8_t v_pu_850_, lean_object* v_as_851_, size_t v_i_852_, size_t v_stop_853_, lean_object* v_b_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___y_862_; uint8_t v___x_868_; 
v___x_868_ = lean_usize_dec_eq(v_i_852_, v_stop_853_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; 
v___x_869_ = lean_array_uget_borrowed(v_as_851_, v_i_852_);
switch(lean_obj_tag(v___x_869_))
{
case 0:
{
lean_object* v_code_870_; 
v_code_870_ = lean_ctor_get(v___x_869_, 2);
lean_inc_ref(v_code_870_);
v___y_862_ = v_code_870_;
goto v___jp_861_;
}
case 1:
{
lean_object* v_code_871_; 
v_code_871_ = lean_ctor_get(v___x_869_, 1);
lean_inc_ref(v_code_871_);
v___y_862_ = v_code_871_;
goto v___jp_861_;
}
default: 
{
lean_object* v_code_872_; 
v_code_872_ = lean_ctor_get(v___x_869_, 0);
lean_inc_ref(v_code_872_);
v___y_862_ = v_code_872_;
goto v___jp_861_;
}
}
}
else
{
lean_object* v___x_873_; 
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v_b_854_);
return v___x_873_;
}
v___jp_861_:
{
lean_object* v___x_863_; 
v___x_863_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_850_, v___y_862_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; size_t v___x_865_; size_t v___x_866_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_863_, 1);
v___x_865_ = ((size_t)1ULL);
v___x_866_ = lean_usize_add(v_i_852_, v___x_865_);
v_i_852_ = v___x_866_;
v_b_854_ = v_a_864_;
goto _start;
}
else
{
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0___boxed(lean_object* v_pu_874_, lean_object* v_as_875_, lean_object* v_i_876_, lean_object* v_stop_877_, lean_object* v_b_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
uint8_t v_pu_boxed_885_; size_t v_i_boxed_886_; size_t v_stop_boxed_887_; lean_object* v_res_888_; 
v_pu_boxed_885_ = lean_unbox(v_pu_874_);
v_i_boxed_886_ = lean_unbox_usize(v_i_876_);
lean_dec(v_i_876_);
v_stop_boxed_887_ = lean_unbox_usize(v_stop_877_);
lean_dec(v_stop_877_);
v_res_888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_boxed_885_, v_as_875_, v_i_boxed_886_, v_stop_boxed_887_, v_b_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v_as_875_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go___boxed(lean_object* v_pu_889_, lean_object* v_c_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
uint8_t v_pu_boxed_897_; lean_object* v_res_898_; 
v_pu_boxed_897_ = lean_unbox(v_pu_889_);
v_res_898_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_boxed_897_, v_c_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(lean_object* v_f_899_, lean_object* v_v_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
if (lean_obj_tag(v_v_900_) == 0)
{
lean_object* v_code_907_; lean_object* v___x_908_; 
v_code_907_ = lean_ctor_get(v_v_900_, 0);
lean_inc_ref(v_code_907_);
lean_dec_ref_known(v_v_900_, 1);
lean_inc(v___y_905_);
lean_inc_ref(v___y_904_);
lean_inc(v___y_903_);
lean_inc_ref(v___y_902_);
lean_inc(v___y_901_);
v___x_908_ = lean_apply_7(v_f_899_, v_code_907_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, lean_box(0));
return v___x_908_;
}
else
{
lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_916_; 
lean_dec_ref(v_f_899_);
v_isSharedCheck_916_ = !lean_is_exclusive(v_v_900_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; 
v_unused_917_ = lean_ctor_get(v_v_900_, 0);
lean_dec(v_unused_917_);
v___x_910_ = v_v_900_;
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
else
{
lean_dec(v_v_900_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_912_ = lean_box(0);
if (v_isShared_911_ == 0)
{
lean_ctor_set_tag(v___x_910_, 0);
lean_ctor_set(v___x_910_, 0, v___x_912_);
v___x_914_ = v___x_910_;
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg___boxed(lean_object* v_f_918_, lean_object* v_v_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v_f_918_, v_v_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0(uint8_t v_pu_927_, lean_object* v_f_928_, lean_object* v_v_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v_f_928_, v_v_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___boxed(lean_object* v_pu_937_, lean_object* v_f_938_, lean_object* v_v_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
uint8_t v_pu_boxed_946_; lean_object* v_res_947_; 
v_pu_boxed_946_ = lean_unbox(v_pu_937_);
v_res_947_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0(v_pu_boxed_946_, v_f_938_, v_v_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(uint8_t v_pu_948_, lean_object* v_as_949_, size_t v_i_950_, size_t v_stop_951_, lean_object* v_b_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
uint8_t v___x_959_; 
v___x_959_ = lean_usize_dec_eq(v_i_950_, v_stop_951_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v_value_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_960_ = lean_array_uget_borrowed(v_as_949_, v_i_950_);
v_value_961_ = lean_ctor_get(v___x_960_, 1);
v___x_962_ = lean_box(v_pu_948_);
v___x_963_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go___boxed), 8, 1);
lean_closure_set(v___x_963_, 0, v___x_962_);
lean_inc_ref(v_value_961_);
v___x_964_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v___x_963_, v_value_961_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; size_t v___x_966_; size_t v___x_967_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_964_, 1);
v___x_966_ = ((size_t)1ULL);
v___x_967_ = lean_usize_add(v_i_950_, v___x_966_);
v_i_950_ = v___x_967_;
v_b_952_ = v_a_965_;
goto _start;
}
else
{
return v___x_964_;
}
}
else
{
lean_object* v___x_969_; 
v___x_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_969_, 0, v_b_952_);
return v___x_969_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1___boxed(lean_object* v_pu_970_, lean_object* v_as_971_, lean_object* v_i_972_, lean_object* v_stop_973_, lean_object* v_b_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
uint8_t v_pu_boxed_981_; size_t v_i_boxed_982_; size_t v_stop_boxed_983_; lean_object* v_res_984_; 
v_pu_boxed_981_ = lean_unbox(v_pu_970_);
v_i_boxed_982_ = lean_unbox_usize(v_i_972_);
lean_dec(v_i_972_);
v_stop_boxed_983_ = lean_unbox_usize(v_stop_973_);
lean_dec(v_stop_973_);
v_res_984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_boxed_981_, v_as_971_, v_i_boxed_982_, v_stop_boxed_983_, v_b_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v_as_971_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(uint8_t v_pu_985_, lean_object* v_decls_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_array_get_size(v_decls_986_);
v___x_995_ = lean_box(0);
v___x_996_ = lean_nat_dec_lt(v___x_993_, v___x_994_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; 
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
return v___x_997_;
}
else
{
uint8_t v___x_998_; 
v___x_998_ = lean_nat_dec_le(v___x_994_, v___x_994_);
if (v___x_998_ == 0)
{
if (v___x_996_ == 0)
{
lean_object* v___x_999_; 
v___x_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_999_, 0, v___x_995_);
return v___x_999_;
}
else
{
size_t v___x_1000_; size_t v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = ((size_t)0ULL);
v___x_1001_ = lean_usize_of_nat(v___x_994_);
v___x_1002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_985_, v_decls_986_, v___x_1000_, v___x_1001_, v___x_995_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
return v___x_1002_;
}
}
else
{
size_t v___x_1003_; size_t v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = ((size_t)0ULL);
v___x_1004_ = lean_usize_of_nat(v___x_994_);
v___x_1005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_985_, v_decls_986_, v___x_1003_, v___x_1004_, v___x_995_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
return v___x_1005_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start___boxed(lean_object* v_pu_1006_, lean_object* v_decls_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
uint8_t v_pu_boxed_1014_; lean_object* v_res_1015_; 
v_pu_boxed_1014_ = lean_unbox(v_pu_1006_);
v_res_1015_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(v_pu_boxed_1014_, v_decls_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_decls_1007_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getLetValues(uint8_t v_pu_1018_, lean_object* v_decls_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_getLetValues___closed__0));
v___x_1026_ = lean_st_mk_ref(v___x_1025_);
v___x_1027_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(v_pu_1018_, v_decls_1019_, v___x_1026_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1035_; 
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1035_ == 0)
{
lean_object* v_unused_1036_; 
v_unused_1036_ = lean_ctor_get(v___x_1027_, 0);
lean_dec(v_unused_1036_);
v___x_1029_ = v___x_1027_;
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
else
{
lean_dec(v___x_1027_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1031_ = lean_st_ref_get(v___x_1026_);
lean_dec(v___x_1026_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1031_);
v___x_1033_ = v___x_1029_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec(v___x_1026_);
v_a_1037_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1027_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1027_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getLetValues___boxed(lean_object* v_pu_1045_, lean_object* v_decls_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
uint8_t v_pu_boxed_1052_; lean_object* v_res_1053_; 
v_pu_boxed_1052_ = lean_unbox(v_pu_1045_);
v_res_1053_ = l_Lean_Compiler_LCNF_Probe_getLetValues(v_pu_boxed_1052_, v_decls_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec_ref(v_decls_1046_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(uint8_t v_pu_1054_, lean_object* v_code_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
switch(lean_obj_tag(v_code_1055_))
{
case 0:
{
lean_object* v_k_1062_; 
v_k_1062_ = lean_ctor_get(v_code_1055_, 1);
lean_inc_ref(v_k_1062_);
lean_dec_ref_known(v_code_1055_, 2);
v_code_1055_ = v_k_1062_;
goto _start;
}
case 1:
{
lean_object* v_decl_1064_; lean_object* v_k_1065_; lean_object* v_value_1066_; lean_object* v___x_1067_; 
v_decl_1064_ = lean_ctor_get(v_code_1055_, 0);
lean_inc_ref(v_decl_1064_);
v_k_1065_ = lean_ctor_get(v_code_1055_, 1);
lean_inc_ref(v_k_1065_);
lean_dec_ref_known(v_code_1055_, 2);
v_value_1066_ = lean_ctor_get(v_decl_1064_, 4);
lean_inc_ref(v_value_1066_);
lean_dec_ref(v_decl_1064_);
v___x_1067_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1054_, v_value_1066_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_dec_ref_known(v___x_1067_, 1);
v_code_1055_ = v_k_1065_;
goto _start;
}
else
{
lean_dec_ref(v_k_1065_);
return v___x_1067_;
}
}
case 2:
{
lean_object* v_decl_1069_; lean_object* v_k_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v_value_1074_; lean_object* v___x_1075_; 
v_decl_1069_ = lean_ctor_get(v_code_1055_, 0);
lean_inc_ref_n(v_decl_1069_, 2);
v_k_1070_ = lean_ctor_get(v_code_1055_, 1);
lean_inc_ref(v_k_1070_);
lean_dec_ref_known(v_code_1055_, 2);
v___x_1071_ = lean_st_ref_take(v_a_1056_);
v___x_1072_ = lean_array_push(v___x_1071_, v_decl_1069_);
v___x_1073_ = lean_st_ref_put(v_a_1056_, v___x_1072_);
v_value_1074_ = lean_ctor_get(v_decl_1069_, 4);
lean_inc_ref(v_value_1074_);
lean_dec_ref(v_decl_1069_);
v___x_1075_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1054_, v_value_1074_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_dec_ref_known(v___x_1075_, 1);
v_code_1055_ = v_k_1070_;
goto _start;
}
else
{
lean_dec_ref(v_k_1070_);
return v___x_1075_;
}
}
case 4:
{
lean_object* v_cases_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1099_; 
v_cases_1077_ = lean_ctor_get(v_code_1055_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_code_1055_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1079_ = v_code_1055_;
v_isShared_1080_ = v_isSharedCheck_1099_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_cases_1077_);
lean_dec(v_code_1055_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1099_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v_alts_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v_alts_1081_ = lean_ctor_get(v_cases_1077_, 3);
lean_inc_ref(v_alts_1081_);
lean_dec_ref(v_cases_1077_);
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = lean_array_get_size(v_alts_1081_);
v___x_1084_ = lean_box(0);
v___x_1085_ = lean_nat_dec_lt(v___x_1082_, v___x_1083_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1087_; 
lean_dec_ref(v_alts_1081_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set_tag(v___x_1079_, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1084_);
v___x_1087_ = v___x_1079_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1084_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
else
{
uint8_t v___x_1089_; 
v___x_1089_ = lean_nat_dec_le(v___x_1083_, v___x_1083_);
if (v___x_1089_ == 0)
{
if (v___x_1085_ == 0)
{
lean_object* v___x_1091_; 
lean_dec_ref(v_alts_1081_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set_tag(v___x_1079_, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1084_);
v___x_1091_ = v___x_1079_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1084_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
else
{
size_t v___x_1093_; size_t v___x_1094_; lean_object* v___x_1095_; 
lean_del_object(v___x_1079_);
v___x_1093_ = ((size_t)0ULL);
v___x_1094_ = lean_usize_of_nat(v___x_1083_);
v___x_1095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_1054_, v_alts_1081_, v___x_1093_, v___x_1094_, v___x_1084_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
lean_dec_ref(v_alts_1081_);
return v___x_1095_;
}
}
else
{
size_t v___x_1096_; size_t v___x_1097_; lean_object* v___x_1098_; 
lean_del_object(v___x_1079_);
v___x_1096_ = ((size_t)0ULL);
v___x_1097_ = lean_usize_of_nat(v___x_1083_);
v___x_1098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_1054_, v_alts_1081_, v___x_1096_, v___x_1097_, v___x_1084_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
lean_dec_ref(v_alts_1081_);
return v___x_1098_;
}
}
}
}
case 7:
{
lean_object* v_k_1100_; 
v_k_1100_ = lean_ctor_get(v_code_1055_, 3);
lean_inc_ref(v_k_1100_);
lean_dec_ref_known(v_code_1055_, 4);
v_code_1055_ = v_k_1100_;
goto _start;
}
case 8:
{
lean_object* v_k_1102_; 
v_k_1102_ = lean_ctor_get(v_code_1055_, 3);
lean_inc_ref(v_k_1102_);
lean_dec_ref_known(v_code_1055_, 4);
v_code_1055_ = v_k_1102_;
goto _start;
}
case 9:
{
lean_object* v_k_1104_; 
v_k_1104_ = lean_ctor_get(v_code_1055_, 5);
lean_inc_ref(v_k_1104_);
lean_dec_ref_known(v_code_1055_, 6);
v_code_1055_ = v_k_1104_;
goto _start;
}
case 10:
{
lean_object* v_k_1106_; 
v_k_1106_ = lean_ctor_get(v_code_1055_, 2);
lean_inc_ref(v_k_1106_);
lean_dec_ref_known(v_code_1055_, 3);
v_code_1055_ = v_k_1106_;
goto _start;
}
case 11:
{
lean_object* v_k_1108_; 
v_k_1108_ = lean_ctor_get(v_code_1055_, 2);
lean_inc_ref(v_k_1108_);
lean_dec_ref_known(v_code_1055_, 3);
v_code_1055_ = v_k_1108_;
goto _start;
}
case 12:
{
lean_object* v_k_1110_; 
v_k_1110_ = lean_ctor_get(v_code_1055_, 3);
lean_inc_ref(v_k_1110_);
lean_dec_ref_known(v_code_1055_, 4);
v_code_1055_ = v_k_1110_;
goto _start;
}
case 13:
{
lean_object* v_k_1112_; 
v_k_1112_ = lean_ctor_get(v_code_1055_, 1);
lean_inc_ref(v_k_1112_);
lean_dec_ref_known(v_code_1055_, 2);
v_code_1055_ = v_k_1112_;
goto _start;
}
default: 
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_dec_ref(v_code_1055_);
v___x_1114_ = lean_box(0);
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
return v___x_1115_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(uint8_t v_pu_1116_, lean_object* v_as_1117_, size_t v_i_1118_, size_t v_stop_1119_, lean_object* v_b_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___y_1128_; uint8_t v___x_1134_; 
v___x_1134_ = lean_usize_dec_eq(v_i_1118_, v_stop_1119_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_array_uget_borrowed(v_as_1117_, v_i_1118_);
switch(lean_obj_tag(v___x_1135_))
{
case 0:
{
lean_object* v_code_1136_; 
v_code_1136_ = lean_ctor_get(v___x_1135_, 2);
lean_inc_ref(v_code_1136_);
v___y_1128_ = v_code_1136_;
goto v___jp_1127_;
}
case 1:
{
lean_object* v_code_1137_; 
v_code_1137_ = lean_ctor_get(v___x_1135_, 1);
lean_inc_ref(v_code_1137_);
v___y_1128_ = v_code_1137_;
goto v___jp_1127_;
}
default: 
{
lean_object* v_code_1138_; 
v_code_1138_ = lean_ctor_get(v___x_1135_, 0);
lean_inc_ref(v_code_1138_);
v___y_1128_ = v_code_1138_;
goto v___jp_1127_;
}
}
}
else
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v_b_1120_);
return v___x_1139_;
}
v___jp_1127_:
{
lean_object* v___x_1129_; 
v___x_1129_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1116_, v___y_1128_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; size_t v___x_1131_; size_t v___x_1132_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1129_, 1);
v___x_1131_ = ((size_t)1ULL);
v___x_1132_ = lean_usize_add(v_i_1118_, v___x_1131_);
v_i_1118_ = v___x_1132_;
v_b_1120_ = v_a_1130_;
goto _start;
}
else
{
return v___x_1129_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0___boxed(lean_object* v_pu_1140_, lean_object* v_as_1141_, lean_object* v_i_1142_, lean_object* v_stop_1143_, lean_object* v_b_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
uint8_t v_pu_boxed_1151_; size_t v_i_boxed_1152_; size_t v_stop_boxed_1153_; lean_object* v_res_1154_; 
v_pu_boxed_1151_ = lean_unbox(v_pu_1140_);
v_i_boxed_1152_ = lean_unbox_usize(v_i_1142_);
lean_dec(v_i_1142_);
v_stop_boxed_1153_ = lean_unbox_usize(v_stop_1143_);
lean_dec(v_stop_1143_);
v_res_1154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_boxed_1151_, v_as_1141_, v_i_boxed_1152_, v_stop_boxed_1153_, v_b_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v_as_1141_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go___boxed(lean_object* v_pu_1155_, lean_object* v_code_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
uint8_t v_pu_boxed_1163_; lean_object* v_res_1164_; 
v_pu_boxed_1163_ = lean_unbox(v_pu_1155_);
v_res_1164_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_boxed_1163_, v_code_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(lean_object* v_f_1165_, lean_object* v_v_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
if (lean_obj_tag(v_v_1166_) == 0)
{
lean_object* v_code_1173_; lean_object* v___x_1174_; 
v_code_1173_ = lean_ctor_get(v_v_1166_, 0);
lean_inc_ref(v_code_1173_);
lean_dec_ref_known(v_v_1166_, 1);
lean_inc(v___y_1171_);
lean_inc_ref(v___y_1170_);
lean_inc(v___y_1169_);
lean_inc_ref(v___y_1168_);
lean_inc(v___y_1167_);
v___x_1174_ = lean_apply_7(v_f_1165_, v_code_1173_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, lean_box(0));
return v___x_1174_;
}
else
{
lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1182_; 
lean_dec_ref(v_f_1165_);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_v_1166_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; 
v_unused_1183_ = lean_ctor_get(v_v_1166_, 0);
lean_dec(v_unused_1183_);
v___x_1176_ = v_v_1166_;
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
else
{
lean_dec(v_v_1166_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = lean_box(0);
if (v_isShared_1177_ == 0)
{
lean_ctor_set_tag(v___x_1176_, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1178_);
v___x_1180_ = v___x_1176_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg___boxed(lean_object* v_f_1184_, lean_object* v_v_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v_f_1184_, v_v_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0(uint8_t v_pu_1193_, lean_object* v_f_1194_, lean_object* v_v_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v_f_1194_, v_v_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___boxed(lean_object* v_pu_1203_, lean_object* v_f_1204_, lean_object* v_v_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
uint8_t v_pu_boxed_1212_; lean_object* v_res_1213_; 
v_pu_boxed_1212_ = lean_unbox(v_pu_1203_);
v_res_1213_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0(v_pu_boxed_1212_, v_f_1204_, v_v_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(uint8_t v_pu_1214_, lean_object* v_as_1215_, size_t v_i_1216_, size_t v_stop_1217_, lean_object* v_b_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
uint8_t v___x_1225_; 
v___x_1225_ = lean_usize_dec_eq(v_i_1216_, v_stop_1217_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v_value_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1226_ = lean_array_uget_borrowed(v_as_1215_, v_i_1216_);
v_value_1227_ = lean_ctor_get(v___x_1226_, 1);
v___x_1228_ = lean_box(v_pu_1214_);
v___x_1229_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go___boxed), 8, 1);
lean_closure_set(v___x_1229_, 0, v___x_1228_);
lean_inc_ref(v_value_1227_);
v___x_1230_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v___x_1229_, v_value_1227_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; size_t v___x_1232_; size_t v___x_1233_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1231_);
lean_dec_ref_known(v___x_1230_, 1);
v___x_1232_ = ((size_t)1ULL);
v___x_1233_ = lean_usize_add(v_i_1216_, v___x_1232_);
v_i_1216_ = v___x_1233_;
v_b_1218_ = v_a_1231_;
goto _start;
}
else
{
return v___x_1230_;
}
}
else
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v_b_1218_);
return v___x_1235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1___boxed(lean_object* v_pu_1236_, lean_object* v_as_1237_, lean_object* v_i_1238_, lean_object* v_stop_1239_, lean_object* v_b_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
uint8_t v_pu_boxed_1247_; size_t v_i_boxed_1248_; size_t v_stop_boxed_1249_; lean_object* v_res_1250_; 
v_pu_boxed_1247_ = lean_unbox(v_pu_1236_);
v_i_boxed_1248_ = lean_unbox_usize(v_i_1238_);
lean_dec(v_i_1238_);
v_stop_boxed_1249_ = lean_unbox_usize(v_stop_1239_);
lean_dec(v_stop_1239_);
v_res_1250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_boxed_1247_, v_as_1237_, v_i_boxed_1248_, v_stop_boxed_1249_, v_b_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v_as_1237_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(uint8_t v_pu_1251_, lean_object* v_decls_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1259_ = lean_unsigned_to_nat(0u);
v___x_1260_ = lean_array_get_size(v_decls_1252_);
v___x_1261_ = lean_box(0);
v___x_1262_ = lean_nat_dec_lt(v___x_1259_, v___x_1260_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; 
v___x_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1261_);
return v___x_1263_;
}
else
{
uint8_t v___x_1264_; 
v___x_1264_ = lean_nat_dec_le(v___x_1260_, v___x_1260_);
if (v___x_1264_ == 0)
{
if (v___x_1262_ == 0)
{
lean_object* v___x_1265_; 
v___x_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1261_);
return v___x_1265_;
}
else
{
size_t v___x_1266_; size_t v___x_1267_; lean_object* v___x_1268_; 
v___x_1266_ = ((size_t)0ULL);
v___x_1267_ = lean_usize_of_nat(v___x_1260_);
v___x_1268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_1251_, v_decls_1252_, v___x_1266_, v___x_1267_, v___x_1261_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
return v___x_1268_;
}
}
else
{
size_t v___x_1269_; size_t v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = ((size_t)0ULL);
v___x_1270_ = lean_usize_of_nat(v___x_1260_);
v___x_1271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_1251_, v_decls_1252_, v___x_1269_, v___x_1270_, v___x_1261_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
return v___x_1271_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start___boxed(lean_object* v_pu_1272_, lean_object* v_decls_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
uint8_t v_pu_boxed_1280_; lean_object* v_res_1281_; 
v_pu_boxed_1280_ = lean_unbox(v_pu_1272_);
v_res_1281_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(v_pu_boxed_1280_, v_decls_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_decls_1273_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getJps(uint8_t v_pu_1284_, lean_object* v_decls_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1291_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_getJps___closed__0));
v___x_1292_ = lean_st_mk_ref(v___x_1291_);
v___x_1293_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(v_pu_1284_, v_decls_1285_, v___x_1292_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1301_; 
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1301_ == 0)
{
lean_object* v_unused_1302_; 
v_unused_1302_ = lean_ctor_get(v___x_1293_, 0);
lean_dec(v_unused_1302_);
v___x_1295_ = v___x_1293_;
v_isShared_1296_ = v_isSharedCheck_1301_;
goto v_resetjp_1294_;
}
else
{
lean_dec(v___x_1293_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1301_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1297_ = lean_st_ref_get(v___x_1292_);
lean_dec(v___x_1292_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1297_);
v___x_1299_ = v___x_1295_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec(v___x_1292_);
v_a_1303_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1293_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1293_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getJps___boxed(lean_object* v_pu_1311_, lean_object* v_decls_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
uint8_t v_pu_boxed_1318_; lean_object* v_res_1319_; 
v_pu_boxed_1318_ = lean_unbox(v_pu_1311_);
v_res_1319_ = l_Lean_Compiler_LCNF_Probe_getJps(v_pu_boxed_1318_, v_decls_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec_ref(v_decls_1312_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(uint8_t v_pu_1320_, lean_object* v_f_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_){
_start:
{
switch(lean_obj_tag(v_a_1322_))
{
case 0:
{
lean_object* v_decl_1328_; lean_object* v_k_1329_; lean_object* v___x_1330_; 
v_decl_1328_ = lean_ctor_get(v_a_1322_, 0);
lean_inc_ref(v_decl_1328_);
v_k_1329_ = lean_ctor_get(v_a_1322_, 1);
lean_inc_ref(v_k_1329_);
lean_dec_ref_known(v_a_1322_, 2);
lean_inc_ref(v_f_1321_);
lean_inc(v_a_1326_);
lean_inc_ref(v_a_1325_);
lean_inc(v_a_1324_);
lean_inc_ref(v_a_1323_);
v___x_1330_ = lean_apply_6(v_f_1321_, v_decl_1328_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, lean_box(0));
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; uint8_t v___x_1332_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
v___x_1332_ = lean_unbox(v_a_1331_);
lean_dec(v_a_1331_);
if (v___x_1332_ == 0)
{
lean_dec_ref_known(v___x_1330_, 1);
v_a_1322_ = v_k_1329_;
goto _start;
}
else
{
lean_dec_ref(v_k_1329_);
lean_dec_ref(v_f_1321_);
return v___x_1330_;
}
}
else
{
lean_dec_ref(v_k_1329_);
lean_dec_ref(v_f_1321_);
return v___x_1330_;
}
}
case 1:
{
lean_object* v_decl_1334_; lean_object* v_k_1335_; lean_object* v_value_1336_; lean_object* v___x_1337_; 
v_decl_1334_ = lean_ctor_get(v_a_1322_, 0);
lean_inc_ref(v_decl_1334_);
v_k_1335_ = lean_ctor_get(v_a_1322_, 1);
lean_inc_ref(v_k_1335_);
lean_dec_ref_known(v_a_1322_, 2);
v_value_1336_ = lean_ctor_get(v_decl_1334_, 4);
lean_inc_ref(v_value_1336_);
lean_dec_ref(v_decl_1334_);
lean_inc_ref(v_f_1321_);
v___x_1337_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1320_, v_f_1321_, v_value_1336_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; uint8_t v___x_1339_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
v___x_1339_ = lean_unbox(v_a_1338_);
lean_dec(v_a_1338_);
if (v___x_1339_ == 0)
{
lean_dec_ref_known(v___x_1337_, 1);
v_a_1322_ = v_k_1335_;
goto _start;
}
else
{
lean_dec_ref(v_k_1335_);
lean_dec_ref(v_f_1321_);
return v___x_1337_;
}
}
else
{
lean_dec_ref(v_k_1335_);
lean_dec_ref(v_f_1321_);
return v___x_1337_;
}
}
case 2:
{
lean_object* v_decl_1341_; lean_object* v_k_1342_; lean_object* v_value_1343_; lean_object* v___x_1344_; 
v_decl_1341_ = lean_ctor_get(v_a_1322_, 0);
lean_inc_ref(v_decl_1341_);
v_k_1342_ = lean_ctor_get(v_a_1322_, 1);
lean_inc_ref(v_k_1342_);
lean_dec_ref_known(v_a_1322_, 2);
v_value_1343_ = lean_ctor_get(v_decl_1341_, 4);
lean_inc_ref(v_value_1343_);
lean_dec_ref(v_decl_1341_);
lean_inc_ref(v_f_1321_);
v___x_1344_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1320_, v_f_1321_, v_value_1343_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
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
v_a_1322_ = v_k_1342_;
goto _start;
}
else
{
lean_dec_ref(v_k_1342_);
lean_dec_ref(v_f_1321_);
return v___x_1344_;
}
}
else
{
lean_dec_ref(v_k_1342_);
lean_dec_ref(v_f_1321_);
return v___x_1344_;
}
}
case 4:
{
lean_object* v_cases_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1367_; 
v_cases_1348_ = lean_ctor_get(v_a_1322_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_a_1322_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1350_ = v_a_1322_;
v_isShared_1351_ = v_isSharedCheck_1367_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_cases_1348_);
lean_dec(v_a_1322_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1367_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v_alts_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v_alts_1352_ = lean_ctor_get(v_cases_1348_, 3);
lean_inc_ref(v_alts_1352_);
lean_dec_ref(v_cases_1348_);
v___x_1353_ = lean_unsigned_to_nat(0u);
v___x_1354_ = lean_array_get_size(v_alts_1352_);
v___x_1355_ = lean_nat_dec_lt(v___x_1353_, v___x_1354_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
lean_dec_ref(v_alts_1352_);
lean_dec_ref(v_f_1321_);
v___x_1356_ = lean_box(v___x_1355_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set_tag(v___x_1350_, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1356_);
v___x_1358_ = v___x_1350_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
else
{
if (v___x_1355_ == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1362_; 
lean_dec_ref(v_alts_1352_);
lean_dec_ref(v_f_1321_);
v___x_1360_ = lean_box(v___x_1355_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set_tag(v___x_1350_, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1360_);
v___x_1362_ = v___x_1350_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
else
{
size_t v___x_1364_; size_t v___x_1365_; lean_object* v___x_1366_; 
lean_del_object(v___x_1350_);
v___x_1364_ = ((size_t)0ULL);
v___x_1365_ = lean_usize_of_nat(v___x_1354_);
v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(v_pu_1320_, v_f_1321_, v_alts_1352_, v___x_1364_, v___x_1365_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
lean_dec_ref(v_alts_1352_);
return v___x_1366_;
}
}
}
}
case 7:
{
lean_object* v_k_1368_; 
v_k_1368_ = lean_ctor_get(v_a_1322_, 3);
lean_inc_ref(v_k_1368_);
lean_dec_ref_known(v_a_1322_, 4);
v_a_1322_ = v_k_1368_;
goto _start;
}
case 8:
{
lean_object* v_k_1370_; 
v_k_1370_ = lean_ctor_get(v_a_1322_, 3);
lean_inc_ref(v_k_1370_);
lean_dec_ref_known(v_a_1322_, 4);
v_a_1322_ = v_k_1370_;
goto _start;
}
case 9:
{
lean_object* v_k_1372_; 
v_k_1372_ = lean_ctor_get(v_a_1322_, 5);
lean_inc_ref(v_k_1372_);
lean_dec_ref_known(v_a_1322_, 6);
v_a_1322_ = v_k_1372_;
goto _start;
}
case 10:
{
lean_object* v_k_1374_; 
v_k_1374_ = lean_ctor_get(v_a_1322_, 2);
lean_inc_ref(v_k_1374_);
lean_dec_ref_known(v_a_1322_, 3);
v_a_1322_ = v_k_1374_;
goto _start;
}
case 11:
{
lean_object* v_k_1376_; 
v_k_1376_ = lean_ctor_get(v_a_1322_, 2);
lean_inc_ref(v_k_1376_);
lean_dec_ref_known(v_a_1322_, 3);
v_a_1322_ = v_k_1376_;
goto _start;
}
case 12:
{
lean_object* v_k_1378_; 
v_k_1378_ = lean_ctor_get(v_a_1322_, 3);
lean_inc_ref(v_k_1378_);
lean_dec_ref_known(v_a_1322_, 4);
v_a_1322_ = v_k_1378_;
goto _start;
}
case 13:
{
lean_object* v_k_1380_; 
v_k_1380_ = lean_ctor_get(v_a_1322_, 1);
lean_inc_ref(v_k_1380_);
lean_dec_ref_known(v_a_1322_, 2);
v_a_1322_ = v_k_1380_;
goto _start;
}
default: 
{
uint8_t v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_dec_ref(v_a_1322_);
lean_dec_ref(v_f_1321_);
v___x_1382_ = 0;
v___x_1383_ = lean_box(v___x_1382_);
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(uint8_t v_pu_1385_, lean_object* v_f_1386_, lean_object* v_as_1387_, size_t v_i_1388_, size_t v_stop_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
uint8_t v___x_1395_; 
v___x_1395_ = lean_usize_dec_eq(v_i_1388_, v_stop_1389_);
if (v___x_1395_ == 0)
{
uint8_t v___x_1396_; lean_object* v___y_1398_; lean_object* v___x_1413_; 
v___x_1396_ = 1;
v___x_1413_ = lean_array_uget_borrowed(v_as_1387_, v_i_1388_);
switch(lean_obj_tag(v___x_1413_))
{
case 0:
{
lean_object* v_code_1414_; 
v_code_1414_ = lean_ctor_get(v___x_1413_, 2);
lean_inc_ref(v_code_1414_);
v___y_1398_ = v_code_1414_;
goto v___jp_1397_;
}
case 1:
{
lean_object* v_code_1415_; 
v_code_1415_ = lean_ctor_get(v___x_1413_, 1);
lean_inc_ref(v_code_1415_);
v___y_1398_ = v_code_1415_;
goto v___jp_1397_;
}
default: 
{
lean_object* v_code_1416_; 
v_code_1416_ = lean_ctor_get(v___x_1413_, 0);
lean_inc_ref(v_code_1416_);
v___y_1398_ = v_code_1416_;
goto v___jp_1397_;
}
}
v___jp_1397_:
{
lean_object* v___x_1399_; 
lean_inc_ref(v_f_1386_);
v___x_1399_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1385_, v_f_1386_, v___y_1398_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1412_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1412_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1412_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
uint8_t v___x_1404_; 
v___x_1404_ = lean_unbox(v_a_1400_);
lean_dec(v_a_1400_);
if (v___x_1404_ == 0)
{
size_t v___x_1405_; size_t v___x_1406_; 
lean_del_object(v___x_1402_);
v___x_1405_ = ((size_t)1ULL);
v___x_1406_ = lean_usize_add(v_i_1388_, v___x_1405_);
v_i_1388_ = v___x_1406_;
goto _start;
}
else
{
lean_object* v___x_1408_; lean_object* v___x_1410_; 
lean_dec_ref(v_f_1386_);
v___x_1408_ = lean_box(v___x_1396_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v___x_1408_);
v___x_1410_ = v___x_1402_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
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
lean_dec_ref(v_f_1386_);
return v___x_1399_;
}
}
}
else
{
uint8_t v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
lean_dec_ref(v_f_1386_);
v___x_1417_ = 0;
v___x_1418_ = lean_box(v___x_1417_);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0___boxed(lean_object* v_pu_1420_, lean_object* v_f_1421_, lean_object* v_as_1422_, lean_object* v_i_1423_, lean_object* v_stop_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
uint8_t v_pu_boxed_1430_; size_t v_i_boxed_1431_; size_t v_stop_boxed_1432_; lean_object* v_res_1433_; 
v_pu_boxed_1430_ = lean_unbox(v_pu_1420_);
v_i_boxed_1431_ = lean_unbox_usize(v_i_1423_);
lean_dec(v_i_1423_);
v_stop_boxed_1432_ = lean_unbox_usize(v_stop_1424_);
lean_dec(v_stop_1424_);
v_res_1433_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(v_pu_boxed_1430_, v_f_1421_, v_as_1422_, v_i_boxed_1431_, v_stop_boxed_1432_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec_ref(v_as_1422_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go___boxed(lean_object* v_pu_1434_, lean_object* v_f_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
uint8_t v_pu_boxed_1442_; lean_object* v_res_1443_; 
v_pu_boxed_1442_ = lean_unbox(v_pu_1434_);
v_res_1443_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_boxed_1442_, v_f_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(lean_object* v_v_1444_, lean_object* v_f_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
if (lean_obj_tag(v_v_1444_) == 0)
{
lean_object* v_code_1451_; lean_object* v___x_1452_; 
v_code_1451_ = lean_ctor_get(v_v_1444_, 0);
lean_inc_ref(v_code_1451_);
lean_dec_ref_known(v_v_1444_, 1);
lean_inc(v___y_1449_);
lean_inc_ref(v___y_1448_);
lean_inc(v___y_1447_);
lean_inc_ref(v___y_1446_);
v___x_1452_ = lean_apply_6(v_f_1445_, v_code_1451_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, lean_box(0));
return v___x_1452_;
}
else
{
lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1461_; 
lean_dec_ref(v_f_1445_);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_v_1444_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v_v_1444_, 0);
lean_dec(v_unused_1462_);
v___x_1454_ = v_v_1444_;
v_isShared_1455_ = v_isSharedCheck_1461_;
goto v_resetjp_1453_;
}
else
{
lean_dec(v_v_1444_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1461_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
uint8_t v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1459_; 
v___x_1456_ = 0;
v___x_1457_ = lean_box(v___x_1456_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set_tag(v___x_1454_, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1457_);
v___x_1459_ = v___x_1454_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1457_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg___boxed(lean_object* v_v_1463_, lean_object* v_f_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_v_1463_, v_f_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0(uint8_t v_pu_1471_, lean_object* v_v_1472_, lean_object* v_f_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_v_1472_, v_f_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___boxed(lean_object* v_pu_1480_, lean_object* v_v_1481_, lean_object* v_f_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
uint8_t v_pu_boxed_1488_; lean_object* v_res_1489_; 
v_pu_boxed_1488_ = lean_unbox(v_pu_1480_);
v_res_1489_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0(v_pu_boxed_1488_, v_v_1481_, v_f_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(uint8_t v_pu_1490_, lean_object* v_f_1491_, lean_object* v_as_1492_, size_t v_i_1493_, size_t v_stop_1494_, lean_object* v_b_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_a_1502_; uint8_t v___x_1506_; 
v___x_1506_ = lean_usize_dec_eq(v_i_1493_, v_stop_1494_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; lean_object* v_value_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1507_ = lean_array_uget_borrowed(v_as_1492_, v_i_1493_);
v_value_1508_ = lean_ctor_get(v___x_1507_, 1);
v___x_1509_ = lean_box(v_pu_1490_);
lean_inc_ref(v_f_1491_);
v___x_1510_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go___boxed), 8, 2);
lean_closure_set(v___x_1510_, 0, v___x_1509_);
lean_closure_set(v___x_1510_, 1, v_f_1491_);
lean_inc_ref(v_value_1508_);
v___x_1511_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_1508_, v___x_1510_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; uint8_t v___x_1513_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1511_, 1);
v___x_1513_ = lean_unbox(v_a_1512_);
lean_dec(v_a_1512_);
if (v___x_1513_ == 0)
{
v_a_1502_ = v_b_1495_;
goto v___jp_1501_;
}
else
{
lean_object* v___x_1514_; 
lean_inc(v___x_1507_);
v___x_1514_ = lean_array_push(v_b_1495_, v___x_1507_);
v_a_1502_ = v___x_1514_;
goto v___jp_1501_;
}
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_dec_ref(v_b_1495_);
lean_dec_ref(v_f_1491_);
v_a_1515_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1511_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1511_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
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
lean_object* v___x_1523_; 
lean_dec_ref(v_f_1491_);
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v_b_1495_);
return v___x_1523_;
}
v___jp_1501_:
{
size_t v___x_1503_; size_t v___x_1504_; 
v___x_1503_ = ((size_t)1ULL);
v___x_1504_ = lean_usize_add(v_i_1493_, v___x_1503_);
v_i_1493_ = v___x_1504_;
v_b_1495_ = v_a_1502_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1___boxed(lean_object* v_pu_1524_, lean_object* v_f_1525_, lean_object* v_as_1526_, lean_object* v_i_1527_, lean_object* v_stop_1528_, lean_object* v_b_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
uint8_t v_pu_boxed_1535_; size_t v_i_boxed_1536_; size_t v_stop_boxed_1537_; lean_object* v_res_1538_; 
v_pu_boxed_1535_ = lean_unbox(v_pu_1524_);
v_i_boxed_1536_ = lean_unbox_usize(v_i_1527_);
lean_dec(v_i_1527_);
v_stop_boxed_1537_ = lean_unbox_usize(v_stop_1528_);
lean_dec(v_stop_1528_);
v_res_1538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_boxed_1535_, v_f_1525_, v_as_1526_, v_i_boxed_1536_, v_stop_boxed_1537_, v_b_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec_ref(v_as_1526_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByLet(uint8_t v_pu_1541_, lean_object* v_f_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1549_ = lean_unsigned_to_nat(0u);
v___x_1550_ = lean_array_get_size(v_a_1543_);
v___x_1551_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_1552_ = lean_nat_dec_lt(v___x_1549_, v___x_1550_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
lean_dec_ref(v_f_1542_);
v___x_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
return v___x_1553_;
}
else
{
size_t v___x_1554_; size_t v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = ((size_t)0ULL);
v___x_1555_ = lean_usize_of_nat(v___x_1550_);
v___x_1556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_1541_, v_f_1542_, v_a_1543_, v___x_1554_, v___x_1555_, v___x_1551_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
return v___x_1556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByLet___boxed(lean_object* v_pu_1557_, lean_object* v_f_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
uint8_t v_pu_boxed_1565_; lean_object* v_res_1566_; 
v_pu_boxed_1565_ = lean_unbox(v_pu_1557_);
v_res_1566_ = l_Lean_Compiler_LCNF_Probe_filterByLet(v_pu_boxed_1565_, v_f_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
lean_dec_ref(v_a_1559_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(uint8_t v_pu_1567_, lean_object* v_f_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_){
_start:
{
switch(lean_obj_tag(v_a_1569_))
{
case 0:
{
lean_object* v_k_1575_; 
v_k_1575_ = lean_ctor_get(v_a_1569_, 1);
lean_inc_ref(v_k_1575_);
lean_dec_ref_known(v_a_1569_, 2);
v_a_1569_ = v_k_1575_;
goto _start;
}
case 1:
{
lean_object* v_decl_1577_; lean_object* v_k_1578_; lean_object* v___x_1579_; 
v_decl_1577_ = lean_ctor_get(v_a_1569_, 0);
lean_inc_ref_n(v_decl_1577_, 2);
v_k_1578_ = lean_ctor_get(v_a_1569_, 1);
lean_inc_ref(v_k_1578_);
lean_dec_ref_known(v_a_1569_, 2);
lean_inc_ref(v_f_1568_);
lean_inc(v_a_1573_);
lean_inc_ref(v_a_1572_);
lean_inc(v_a_1571_);
lean_inc_ref(v_a_1570_);
v___x_1579_ = lean_apply_6(v_f_1568_, v_decl_1577_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, lean_box(0));
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; uint8_t v___x_1581_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
v___x_1581_ = lean_unbox(v_a_1580_);
lean_dec(v_a_1580_);
if (v___x_1581_ == 0)
{
lean_object* v_value_1582_; lean_object* v___x_1583_; 
lean_dec_ref_known(v___x_1579_, 1);
v_value_1582_ = lean_ctor_get(v_decl_1577_, 4);
lean_inc_ref(v_value_1582_);
lean_dec_ref(v_decl_1577_);
lean_inc_ref(v_f_1568_);
v___x_1583_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_1567_, v_f_1568_, v_value_1582_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; uint8_t v___x_1585_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
v___x_1585_ = lean_unbox(v_a_1584_);
lean_dec(v_a_1584_);
if (v___x_1585_ == 0)
{
lean_dec_ref_known(v___x_1583_, 1);
v_a_1569_ = v_k_1578_;
goto _start;
}
else
{
lean_dec_ref(v_k_1578_);
lean_dec_ref(v_f_1568_);
return v___x_1583_;
}
}
else
{
lean_dec_ref(v_k_1578_);
lean_dec_ref(v_f_1568_);
return v___x_1583_;
}
}
else
{
lean_dec_ref(v_k_1578_);
lean_dec_ref(v_decl_1577_);
lean_dec_ref(v_f_1568_);
return v___x_1579_;
}
}
else
{
lean_dec_ref(v_k_1578_);
lean_dec_ref(v_decl_1577_);
lean_dec_ref(v_f_1568_);
return v___x_1579_;
}
}
case 2:
{
lean_object* v_k_1587_; 
v_k_1587_ = lean_ctor_get(v_a_1569_, 1);
lean_inc_ref(v_k_1587_);
lean_dec_ref_known(v_a_1569_, 2);
v_a_1569_ = v_k_1587_;
goto _start;
}
case 4:
{
lean_object* v_cases_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1608_; 
v_cases_1589_ = lean_ctor_get(v_a_1569_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_a_1569_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1591_ = v_a_1569_;
v_isShared_1592_ = v_isSharedCheck_1608_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_cases_1589_);
lean_dec(v_a_1569_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1608_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v_alts_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; 
v_alts_1593_ = lean_ctor_get(v_cases_1589_, 3);
lean_inc_ref(v_alts_1593_);
lean_dec_ref(v_cases_1589_);
v___x_1594_ = lean_unsigned_to_nat(0u);
v___x_1595_ = lean_array_get_size(v_alts_1593_);
v___x_1596_ = lean_nat_dec_lt(v___x_1594_, v___x_1595_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; lean_object* v___x_1599_; 
lean_dec_ref(v_alts_1593_);
lean_dec_ref(v_f_1568_);
v___x_1597_ = lean_box(v___x_1596_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set_tag(v___x_1591_, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1597_);
v___x_1599_ = v___x_1591_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
else
{
if (v___x_1596_ == 0)
{
lean_object* v___x_1601_; lean_object* v___x_1603_; 
lean_dec_ref(v_alts_1593_);
lean_dec_ref(v_f_1568_);
v___x_1601_ = lean_box(v___x_1596_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set_tag(v___x_1591_, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1601_);
v___x_1603_ = v___x_1591_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
else
{
size_t v___x_1605_; size_t v___x_1606_; lean_object* v___x_1607_; 
lean_del_object(v___x_1591_);
v___x_1605_ = ((size_t)0ULL);
v___x_1606_ = lean_usize_of_nat(v___x_1595_);
v___x_1607_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(v_pu_1567_, v_f_1568_, v_alts_1593_, v___x_1605_, v___x_1606_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_);
lean_dec_ref(v_alts_1593_);
return v___x_1607_;
}
}
}
}
case 7:
{
lean_object* v_k_1609_; 
v_k_1609_ = lean_ctor_get(v_a_1569_, 3);
lean_inc_ref(v_k_1609_);
lean_dec_ref_known(v_a_1569_, 4);
v_a_1569_ = v_k_1609_;
goto _start;
}
case 8:
{
lean_object* v_k_1611_; 
v_k_1611_ = lean_ctor_get(v_a_1569_, 3);
lean_inc_ref(v_k_1611_);
lean_dec_ref_known(v_a_1569_, 4);
v_a_1569_ = v_k_1611_;
goto _start;
}
case 9:
{
lean_object* v_k_1613_; 
v_k_1613_ = lean_ctor_get(v_a_1569_, 5);
lean_inc_ref(v_k_1613_);
lean_dec_ref_known(v_a_1569_, 6);
v_a_1569_ = v_k_1613_;
goto _start;
}
case 10:
{
lean_object* v_k_1615_; 
v_k_1615_ = lean_ctor_get(v_a_1569_, 2);
lean_inc_ref(v_k_1615_);
lean_dec_ref_known(v_a_1569_, 3);
v_a_1569_ = v_k_1615_;
goto _start;
}
case 11:
{
lean_object* v_k_1617_; 
v_k_1617_ = lean_ctor_get(v_a_1569_, 2);
lean_inc_ref(v_k_1617_);
lean_dec_ref_known(v_a_1569_, 3);
v_a_1569_ = v_k_1617_;
goto _start;
}
case 12:
{
lean_object* v_k_1619_; 
v_k_1619_ = lean_ctor_get(v_a_1569_, 3);
lean_inc_ref(v_k_1619_);
lean_dec_ref_known(v_a_1569_, 4);
v_a_1569_ = v_k_1619_;
goto _start;
}
case 13:
{
lean_object* v_k_1621_; 
v_k_1621_ = lean_ctor_get(v_a_1569_, 1);
lean_inc_ref(v_k_1621_);
lean_dec_ref_known(v_a_1569_, 2);
v_a_1569_ = v_k_1621_;
goto _start;
}
default: 
{
uint8_t v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_dec_ref(v_a_1569_);
lean_dec_ref(v_f_1568_);
v___x_1623_ = 0;
v___x_1624_ = lean_box(v___x_1623_);
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
return v___x_1625_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(uint8_t v_pu_1626_, lean_object* v_f_1627_, lean_object* v_as_1628_, size_t v_i_1629_, size_t v_stop_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
uint8_t v___x_1636_; 
v___x_1636_ = lean_usize_dec_eq(v_i_1629_, v_stop_1630_);
if (v___x_1636_ == 0)
{
uint8_t v___x_1637_; lean_object* v___y_1639_; lean_object* v___x_1654_; 
v___x_1637_ = 1;
v___x_1654_ = lean_array_uget_borrowed(v_as_1628_, v_i_1629_);
switch(lean_obj_tag(v___x_1654_))
{
case 0:
{
lean_object* v_code_1655_; 
v_code_1655_ = lean_ctor_get(v___x_1654_, 2);
lean_inc_ref(v_code_1655_);
v___y_1639_ = v_code_1655_;
goto v___jp_1638_;
}
case 1:
{
lean_object* v_code_1656_; 
v_code_1656_ = lean_ctor_get(v___x_1654_, 1);
lean_inc_ref(v_code_1656_);
v___y_1639_ = v_code_1656_;
goto v___jp_1638_;
}
default: 
{
lean_object* v_code_1657_; 
v_code_1657_ = lean_ctor_get(v___x_1654_, 0);
lean_inc_ref(v_code_1657_);
v___y_1639_ = v_code_1657_;
goto v___jp_1638_;
}
}
v___jp_1638_:
{
lean_object* v___x_1640_; 
lean_inc_ref(v_f_1627_);
v___x_1640_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_1626_, v_f_1627_, v___y_1639_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1653_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1653_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1653_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
uint8_t v___x_1645_; 
v___x_1645_ = lean_unbox(v_a_1641_);
lean_dec(v_a_1641_);
if (v___x_1645_ == 0)
{
size_t v___x_1646_; size_t v___x_1647_; 
lean_del_object(v___x_1643_);
v___x_1646_ = ((size_t)1ULL);
v___x_1647_ = lean_usize_add(v_i_1629_, v___x_1646_);
v_i_1629_ = v___x_1647_;
goto _start;
}
else
{
lean_object* v___x_1649_; lean_object* v___x_1651_; 
lean_dec_ref(v_f_1627_);
v___x_1649_ = lean_box(v___x_1637_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1649_);
v___x_1651_ = v___x_1643_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_dec_ref(v_f_1627_);
return v___x_1640_;
}
}
}
else
{
uint8_t v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
lean_dec_ref(v_f_1627_);
v___x_1658_ = 0;
v___x_1659_ = lean_box(v___x_1658_);
v___x_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
return v___x_1660_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0___boxed(lean_object* v_pu_1661_, lean_object* v_f_1662_, lean_object* v_as_1663_, lean_object* v_i_1664_, lean_object* v_stop_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
uint8_t v_pu_boxed_1671_; size_t v_i_boxed_1672_; size_t v_stop_boxed_1673_; lean_object* v_res_1674_; 
v_pu_boxed_1671_ = lean_unbox(v_pu_1661_);
v_i_boxed_1672_ = lean_unbox_usize(v_i_1664_);
lean_dec(v_i_1664_);
v_stop_boxed_1673_ = lean_unbox_usize(v_stop_1665_);
lean_dec(v_stop_1665_);
v_res_1674_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(v_pu_boxed_1671_, v_f_1662_, v_as_1663_, v_i_boxed_1672_, v_stop_boxed_1673_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec_ref(v_as_1663_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go___boxed(lean_object* v_pu_1675_, lean_object* v_f_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
uint8_t v_pu_boxed_1683_; lean_object* v_res_1684_; 
v_pu_boxed_1683_ = lean_unbox(v_pu_1675_);
v_res_1684_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_boxed_1683_, v_f_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(uint8_t v_pu_1685_, lean_object* v_f_1686_, lean_object* v_as_1687_, size_t v_i_1688_, size_t v_stop_1689_, lean_object* v_b_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_a_1697_; uint8_t v___x_1701_; 
v___x_1701_ = lean_usize_dec_eq(v_i_1688_, v_stop_1689_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; lean_object* v_value_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1702_ = lean_array_uget_borrowed(v_as_1687_, v_i_1688_);
v_value_1703_ = lean_ctor_get(v___x_1702_, 1);
v___x_1704_ = lean_box(v_pu_1685_);
lean_inc_ref(v_f_1686_);
v___x_1705_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go___boxed), 8, 2);
lean_closure_set(v___x_1705_, 0, v___x_1704_);
lean_closure_set(v___x_1705_, 1, v_f_1686_);
lean_inc_ref(v_value_1703_);
v___x_1706_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_1703_, v___x_1705_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; uint8_t v___x_1708_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v___x_1706_, 1);
v___x_1708_ = lean_unbox(v_a_1707_);
lean_dec(v_a_1707_);
if (v___x_1708_ == 0)
{
v_a_1697_ = v_b_1690_;
goto v___jp_1696_;
}
else
{
lean_object* v___x_1709_; 
lean_inc(v___x_1702_);
v___x_1709_ = lean_array_push(v_b_1690_, v___x_1702_);
v_a_1697_ = v___x_1709_;
goto v___jp_1696_;
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec_ref(v_b_1690_);
lean_dec_ref(v_f_1686_);
v_a_1710_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1706_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1706_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
else
{
lean_object* v___x_1718_; 
lean_dec_ref(v_f_1686_);
v___x_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1718_, 0, v_b_1690_);
return v___x_1718_;
}
v___jp_1696_:
{
size_t v___x_1698_; size_t v___x_1699_; 
v___x_1698_ = ((size_t)1ULL);
v___x_1699_ = lean_usize_add(v_i_1688_, v___x_1698_);
v_i_1688_ = v___x_1699_;
v_b_1690_ = v_a_1697_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0___boxed(lean_object* v_pu_1719_, lean_object* v_f_1720_, lean_object* v_as_1721_, lean_object* v_i_1722_, lean_object* v_stop_1723_, lean_object* v_b_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
uint8_t v_pu_boxed_1730_; size_t v_i_boxed_1731_; size_t v_stop_boxed_1732_; lean_object* v_res_1733_; 
v_pu_boxed_1730_ = lean_unbox(v_pu_1719_);
v_i_boxed_1731_ = lean_unbox_usize(v_i_1722_);
lean_dec(v_i_1722_);
v_stop_boxed_1732_ = lean_unbox_usize(v_stop_1723_);
lean_dec(v_stop_1723_);
v_res_1733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_boxed_1730_, v_f_1720_, v_as_1721_, v_i_boxed_1731_, v_stop_boxed_1732_, v_b_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec_ref(v_as_1721_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFun(uint8_t v_pu_1734_, lean_object* v_f_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; uint8_t v___x_1745_; 
v___x_1742_ = lean_unsigned_to_nat(0u);
v___x_1743_ = lean_array_get_size(v_a_1736_);
v___x_1744_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_1745_ = lean_nat_dec_lt(v___x_1742_, v___x_1743_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; 
lean_dec_ref(v_f_1735_);
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1744_);
return v___x_1746_;
}
else
{
size_t v___x_1747_; size_t v___x_1748_; lean_object* v___x_1749_; 
v___x_1747_ = ((size_t)0ULL);
v___x_1748_ = lean_usize_of_nat(v___x_1743_);
v___x_1749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_1734_, v_f_1735_, v_a_1736_, v___x_1747_, v___x_1748_, v___x_1744_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_1749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFun___boxed(lean_object* v_pu_1750_, lean_object* v_f_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_){
_start:
{
uint8_t v_pu_boxed_1758_; lean_object* v_res_1759_; 
v_pu_boxed_1758_ = lean_unbox(v_pu_1750_);
v_res_1759_ = l_Lean_Compiler_LCNF_Probe_filterByFun(v_pu_boxed_1758_, v_f_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_);
lean_dec(v_a_1756_);
lean_dec_ref(v_a_1755_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
lean_dec_ref(v_a_1752_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(uint8_t v_pu_1760_, lean_object* v_f_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
switch(lean_obj_tag(v_a_1762_))
{
case 0:
{
lean_object* v_k_1768_; 
v_k_1768_ = lean_ctor_get(v_a_1762_, 1);
lean_inc_ref(v_k_1768_);
lean_dec_ref_known(v_a_1762_, 2);
v_a_1762_ = v_k_1768_;
goto _start;
}
case 1:
{
lean_object* v_decl_1770_; lean_object* v_k_1771_; lean_object* v_value_1772_; lean_object* v___x_1773_; 
v_decl_1770_ = lean_ctor_get(v_a_1762_, 0);
lean_inc_ref(v_decl_1770_);
v_k_1771_ = lean_ctor_get(v_a_1762_, 1);
lean_inc_ref(v_k_1771_);
lean_dec_ref_known(v_a_1762_, 2);
v_value_1772_ = lean_ctor_get(v_decl_1770_, 4);
lean_inc_ref(v_value_1772_);
lean_dec_ref(v_decl_1770_);
lean_inc_ref(v_f_1761_);
v___x_1773_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1760_, v_f_1761_, v_value_1772_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; uint8_t v___x_1775_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
v___x_1775_ = lean_unbox(v_a_1774_);
lean_dec(v_a_1774_);
if (v___x_1775_ == 0)
{
lean_dec_ref_known(v___x_1773_, 1);
v_a_1762_ = v_k_1771_;
goto _start;
}
else
{
lean_dec_ref(v_k_1771_);
lean_dec_ref(v_f_1761_);
return v___x_1773_;
}
}
else
{
lean_dec_ref(v_k_1771_);
lean_dec_ref(v_f_1761_);
return v___x_1773_;
}
}
case 2:
{
lean_object* v_decl_1777_; lean_object* v_k_1778_; lean_object* v___x_1779_; 
v_decl_1777_ = lean_ctor_get(v_a_1762_, 0);
lean_inc_ref_n(v_decl_1777_, 2);
v_k_1778_ = lean_ctor_get(v_a_1762_, 1);
lean_inc_ref(v_k_1778_);
lean_dec_ref_known(v_a_1762_, 2);
lean_inc_ref(v_f_1761_);
lean_inc(v_a_1766_);
lean_inc_ref(v_a_1765_);
lean_inc(v_a_1764_);
lean_inc_ref(v_a_1763_);
v___x_1779_ = lean_apply_6(v_f_1761_, v_decl_1777_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, lean_box(0));
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; uint8_t v___x_1781_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
v___x_1781_ = lean_unbox(v_a_1780_);
lean_dec(v_a_1780_);
if (v___x_1781_ == 0)
{
lean_object* v_value_1782_; lean_object* v___x_1783_; 
lean_dec_ref_known(v___x_1779_, 1);
v_value_1782_ = lean_ctor_get(v_decl_1777_, 4);
lean_inc_ref(v_value_1782_);
lean_dec_ref(v_decl_1777_);
lean_inc_ref(v_f_1761_);
v___x_1783_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1760_, v_f_1761_, v_value_1782_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; uint8_t v___x_1785_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
v___x_1785_ = lean_unbox(v_a_1784_);
lean_dec(v_a_1784_);
if (v___x_1785_ == 0)
{
lean_dec_ref_known(v___x_1783_, 1);
v_a_1762_ = v_k_1778_;
goto _start;
}
else
{
lean_dec_ref(v_k_1778_);
lean_dec_ref(v_f_1761_);
return v___x_1783_;
}
}
else
{
lean_dec_ref(v_k_1778_);
lean_dec_ref(v_f_1761_);
return v___x_1783_;
}
}
else
{
lean_dec_ref(v_k_1778_);
lean_dec_ref(v_decl_1777_);
lean_dec_ref(v_f_1761_);
return v___x_1779_;
}
}
else
{
lean_dec_ref(v_k_1778_);
lean_dec_ref(v_decl_1777_);
lean_dec_ref(v_f_1761_);
return v___x_1779_;
}
}
case 4:
{
lean_object* v_cases_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1806_; 
v_cases_1787_ = lean_ctor_get(v_a_1762_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_a_1762_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1789_ = v_a_1762_;
v_isShared_1790_ = v_isSharedCheck_1806_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_cases_1787_);
lean_dec(v_a_1762_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1806_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v_alts_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v_alts_1791_ = lean_ctor_get(v_cases_1787_, 3);
lean_inc_ref(v_alts_1791_);
lean_dec_ref(v_cases_1787_);
v___x_1792_ = lean_unsigned_to_nat(0u);
v___x_1793_ = lean_array_get_size(v_alts_1791_);
v___x_1794_ = lean_nat_dec_lt(v___x_1792_, v___x_1793_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1797_; 
lean_dec_ref(v_alts_1791_);
lean_dec_ref(v_f_1761_);
v___x_1795_ = lean_box(v___x_1794_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set_tag(v___x_1789_, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1795_);
v___x_1797_ = v___x_1789_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
else
{
if (v___x_1794_ == 0)
{
lean_object* v___x_1799_; lean_object* v___x_1801_; 
lean_dec_ref(v_alts_1791_);
lean_dec_ref(v_f_1761_);
v___x_1799_ = lean_box(v___x_1794_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set_tag(v___x_1789_, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1799_);
v___x_1801_ = v___x_1789_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
else
{
size_t v___x_1803_; size_t v___x_1804_; lean_object* v___x_1805_; 
lean_del_object(v___x_1789_);
v___x_1803_ = ((size_t)0ULL);
v___x_1804_ = lean_usize_of_nat(v___x_1793_);
v___x_1805_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(v_pu_1760_, v_f_1761_, v_alts_1791_, v___x_1803_, v___x_1804_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
lean_dec_ref(v_alts_1791_);
return v___x_1805_;
}
}
}
}
case 7:
{
lean_object* v_k_1807_; 
v_k_1807_ = lean_ctor_get(v_a_1762_, 3);
lean_inc_ref(v_k_1807_);
lean_dec_ref_known(v_a_1762_, 4);
v_a_1762_ = v_k_1807_;
goto _start;
}
case 8:
{
lean_object* v_k_1809_; 
v_k_1809_ = lean_ctor_get(v_a_1762_, 3);
lean_inc_ref(v_k_1809_);
lean_dec_ref_known(v_a_1762_, 4);
v_a_1762_ = v_k_1809_;
goto _start;
}
case 9:
{
lean_object* v_k_1811_; 
v_k_1811_ = lean_ctor_get(v_a_1762_, 5);
lean_inc_ref(v_k_1811_);
lean_dec_ref_known(v_a_1762_, 6);
v_a_1762_ = v_k_1811_;
goto _start;
}
case 10:
{
lean_object* v_k_1813_; 
v_k_1813_ = lean_ctor_get(v_a_1762_, 2);
lean_inc_ref(v_k_1813_);
lean_dec_ref_known(v_a_1762_, 3);
v_a_1762_ = v_k_1813_;
goto _start;
}
case 11:
{
lean_object* v_k_1815_; 
v_k_1815_ = lean_ctor_get(v_a_1762_, 2);
lean_inc_ref(v_k_1815_);
lean_dec_ref_known(v_a_1762_, 3);
v_a_1762_ = v_k_1815_;
goto _start;
}
case 12:
{
lean_object* v_k_1817_; 
v_k_1817_ = lean_ctor_get(v_a_1762_, 3);
lean_inc_ref(v_k_1817_);
lean_dec_ref_known(v_a_1762_, 4);
v_a_1762_ = v_k_1817_;
goto _start;
}
case 13:
{
lean_object* v_k_1819_; 
v_k_1819_ = lean_ctor_get(v_a_1762_, 1);
lean_inc_ref(v_k_1819_);
lean_dec_ref_known(v_a_1762_, 2);
v_a_1762_ = v_k_1819_;
goto _start;
}
default: 
{
uint8_t v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_dec_ref(v_a_1762_);
lean_dec_ref(v_f_1761_);
v___x_1821_ = 0;
v___x_1822_ = lean_box(v___x_1821_);
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
return v___x_1823_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(uint8_t v_pu_1824_, lean_object* v_f_1825_, lean_object* v_as_1826_, size_t v_i_1827_, size_t v_stop_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
uint8_t v___x_1834_; 
v___x_1834_ = lean_usize_dec_eq(v_i_1827_, v_stop_1828_);
if (v___x_1834_ == 0)
{
uint8_t v___x_1835_; lean_object* v___y_1837_; lean_object* v___x_1852_; 
v___x_1835_ = 1;
v___x_1852_ = lean_array_uget_borrowed(v_as_1826_, v_i_1827_);
switch(lean_obj_tag(v___x_1852_))
{
case 0:
{
lean_object* v_code_1853_; 
v_code_1853_ = lean_ctor_get(v___x_1852_, 2);
lean_inc_ref(v_code_1853_);
v___y_1837_ = v_code_1853_;
goto v___jp_1836_;
}
case 1:
{
lean_object* v_code_1854_; 
v_code_1854_ = lean_ctor_get(v___x_1852_, 1);
lean_inc_ref(v_code_1854_);
v___y_1837_ = v_code_1854_;
goto v___jp_1836_;
}
default: 
{
lean_object* v_code_1855_; 
v_code_1855_ = lean_ctor_get(v___x_1852_, 0);
lean_inc_ref(v_code_1855_);
v___y_1837_ = v_code_1855_;
goto v___jp_1836_;
}
}
v___jp_1836_:
{
lean_object* v___x_1838_; 
lean_inc_ref(v_f_1825_);
v___x_1838_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1824_, v_f_1825_, v___y_1837_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1851_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1851_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1851_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
uint8_t v___x_1843_; 
v___x_1843_ = lean_unbox(v_a_1839_);
lean_dec(v_a_1839_);
if (v___x_1843_ == 0)
{
size_t v___x_1844_; size_t v___x_1845_; 
lean_del_object(v___x_1841_);
v___x_1844_ = ((size_t)1ULL);
v___x_1845_ = lean_usize_add(v_i_1827_, v___x_1844_);
v_i_1827_ = v___x_1845_;
goto _start;
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
lean_dec_ref(v_f_1825_);
v___x_1847_ = lean_box(v___x_1835_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v___x_1847_);
v___x_1849_ = v___x_1841_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
else
{
lean_dec_ref(v_f_1825_);
return v___x_1838_;
}
}
}
else
{
uint8_t v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
lean_dec_ref(v_f_1825_);
v___x_1856_ = 0;
v___x_1857_ = lean_box(v___x_1856_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
return v___x_1858_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0___boxed(lean_object* v_pu_1859_, lean_object* v_f_1860_, lean_object* v_as_1861_, lean_object* v_i_1862_, lean_object* v_stop_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
uint8_t v_pu_boxed_1869_; size_t v_i_boxed_1870_; size_t v_stop_boxed_1871_; lean_object* v_res_1872_; 
v_pu_boxed_1869_ = lean_unbox(v_pu_1859_);
v_i_boxed_1870_ = lean_unbox_usize(v_i_1862_);
lean_dec(v_i_1862_);
v_stop_boxed_1871_ = lean_unbox_usize(v_stop_1863_);
lean_dec(v_stop_1863_);
v_res_1872_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(v_pu_boxed_1869_, v_f_1860_, v_as_1861_, v_i_boxed_1870_, v_stop_boxed_1871_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec_ref(v_as_1861_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go___boxed(lean_object* v_pu_1873_, lean_object* v_f_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
uint8_t v_pu_boxed_1881_; lean_object* v_res_1882_; 
v_pu_boxed_1881_ = lean_unbox(v_pu_1873_);
v_res_1882_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_boxed_1881_, v_f_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_);
lean_dec(v_a_1879_);
lean_dec_ref(v_a_1878_);
lean_dec(v_a_1877_);
lean_dec_ref(v_a_1876_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(uint8_t v_pu_1883_, lean_object* v_f_1884_, lean_object* v_as_1885_, size_t v_i_1886_, size_t v_stop_1887_, lean_object* v_b_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v_a_1895_; uint8_t v___x_1899_; 
v___x_1899_ = lean_usize_dec_eq(v_i_1886_, v_stop_1887_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; lean_object* v_value_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1900_ = lean_array_uget_borrowed(v_as_1885_, v_i_1886_);
v_value_1901_ = lean_ctor_get(v___x_1900_, 1);
v___x_1902_ = lean_box(v_pu_1883_);
lean_inc_ref(v_f_1884_);
v___x_1903_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go___boxed), 8, 2);
lean_closure_set(v___x_1903_, 0, v___x_1902_);
lean_closure_set(v___x_1903_, 1, v_f_1884_);
lean_inc_ref(v_value_1901_);
v___x_1904_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_1901_, v___x_1903_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; uint8_t v___x_1906_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
v___x_1906_ = lean_unbox(v_a_1905_);
lean_dec(v_a_1905_);
if (v___x_1906_ == 0)
{
v_a_1895_ = v_b_1888_;
goto v___jp_1894_;
}
else
{
lean_object* v___x_1907_; 
lean_inc(v___x_1900_);
v___x_1907_ = lean_array_push(v_b_1888_, v___x_1900_);
v_a_1895_ = v___x_1907_;
goto v___jp_1894_;
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec_ref(v_b_1888_);
lean_dec_ref(v_f_1884_);
v_a_1908_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1904_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1904_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
else
{
lean_object* v___x_1916_; 
lean_dec_ref(v_f_1884_);
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_b_1888_);
return v___x_1916_;
}
v___jp_1894_:
{
size_t v___x_1896_; size_t v___x_1897_; 
v___x_1896_ = ((size_t)1ULL);
v___x_1897_ = lean_usize_add(v_i_1886_, v___x_1896_);
v_i_1886_ = v___x_1897_;
v_b_1888_ = v_a_1895_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0___boxed(lean_object* v_pu_1917_, lean_object* v_f_1918_, lean_object* v_as_1919_, lean_object* v_i_1920_, lean_object* v_stop_1921_, lean_object* v_b_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
uint8_t v_pu_boxed_1928_; size_t v_i_boxed_1929_; size_t v_stop_boxed_1930_; lean_object* v_res_1931_; 
v_pu_boxed_1928_ = lean_unbox(v_pu_1917_);
v_i_boxed_1929_ = lean_unbox_usize(v_i_1920_);
lean_dec(v_i_1920_);
v_stop_boxed_1930_ = lean_unbox_usize(v_stop_1921_);
lean_dec(v_stop_1921_);
v_res_1931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_boxed_1928_, v_f_1918_, v_as_1919_, v_i_boxed_1929_, v_stop_boxed_1930_, v_b_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec_ref(v_as_1919_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJp(uint8_t v_pu_1932_, lean_object* v_f_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
v___x_1940_ = lean_unsigned_to_nat(0u);
v___x_1941_ = lean_array_get_size(v_a_1934_);
v___x_1942_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_1943_ = lean_nat_dec_lt(v___x_1940_, v___x_1941_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; 
lean_dec_ref(v_f_1933_);
v___x_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1942_);
return v___x_1944_;
}
else
{
size_t v___x_1945_; size_t v___x_1946_; lean_object* v___x_1947_; 
v___x_1945_ = ((size_t)0ULL);
v___x_1946_ = lean_usize_of_nat(v___x_1941_);
v___x_1947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_1932_, v_f_1933_, v_a_1934_, v___x_1945_, v___x_1946_, v___x_1942_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_);
return v___x_1947_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJp___boxed(lean_object* v_pu_1948_, lean_object* v_f_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
uint8_t v_pu_boxed_1956_; lean_object* v_res_1957_; 
v_pu_boxed_1956_ = lean_unbox(v_pu_1948_);
v_res_1957_ = l_Lean_Compiler_LCNF_Probe_filterByJp(v_pu_boxed_1956_, v_f_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec_ref(v_a_1950_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(uint8_t v_pu_1958_, lean_object* v_f_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_){
_start:
{
switch(lean_obj_tag(v_a_1960_))
{
case 0:
{
lean_object* v_k_1966_; 
v_k_1966_ = lean_ctor_get(v_a_1960_, 1);
lean_inc_ref(v_k_1966_);
lean_dec_ref_known(v_a_1960_, 2);
v_a_1960_ = v_k_1966_;
goto _start;
}
case 1:
{
lean_object* v_decl_1968_; lean_object* v_k_1969_; lean_object* v___x_1970_; 
v_decl_1968_ = lean_ctor_get(v_a_1960_, 0);
lean_inc_ref_n(v_decl_1968_, 2);
v_k_1969_ = lean_ctor_get(v_a_1960_, 1);
lean_inc_ref(v_k_1969_);
lean_dec_ref_known(v_a_1960_, 2);
lean_inc_ref(v_f_1959_);
lean_inc(v_a_1964_);
lean_inc_ref(v_a_1963_);
lean_inc(v_a_1962_);
lean_inc_ref(v_a_1961_);
v___x_1970_ = lean_apply_6(v_f_1959_, v_decl_1968_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, lean_box(0));
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; uint8_t v___x_1972_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
v___x_1972_ = lean_unbox(v_a_1971_);
lean_dec(v_a_1971_);
if (v___x_1972_ == 0)
{
lean_object* v_value_1973_; lean_object* v___x_1974_; 
lean_dec_ref_known(v___x_1970_, 1);
v_value_1973_ = lean_ctor_get(v_decl_1968_, 4);
lean_inc_ref(v_value_1973_);
lean_dec_ref(v_decl_1968_);
lean_inc_ref(v_f_1959_);
v___x_1974_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_1958_, v_f_1959_, v_value_1973_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; uint8_t v___x_1976_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
v___x_1976_ = lean_unbox(v_a_1975_);
lean_dec(v_a_1975_);
if (v___x_1976_ == 0)
{
lean_dec_ref_known(v___x_1974_, 1);
v_a_1960_ = v_k_1969_;
goto _start;
}
else
{
lean_dec_ref(v_k_1969_);
lean_dec_ref(v_f_1959_);
return v___x_1974_;
}
}
else
{
lean_dec_ref(v_k_1969_);
lean_dec_ref(v_f_1959_);
return v___x_1974_;
}
}
else
{
lean_dec_ref(v_k_1969_);
lean_dec_ref(v_decl_1968_);
lean_dec_ref(v_f_1959_);
return v___x_1970_;
}
}
else
{
lean_dec_ref(v_k_1969_);
lean_dec_ref(v_decl_1968_);
lean_dec_ref(v_f_1959_);
return v___x_1970_;
}
}
case 2:
{
lean_object* v_decl_1978_; lean_object* v_k_1979_; lean_object* v___x_1980_; 
v_decl_1978_ = lean_ctor_get(v_a_1960_, 0);
lean_inc_ref_n(v_decl_1978_, 2);
v_k_1979_ = lean_ctor_get(v_a_1960_, 1);
lean_inc_ref(v_k_1979_);
lean_dec_ref_known(v_a_1960_, 2);
lean_inc_ref(v_f_1959_);
lean_inc(v_a_1964_);
lean_inc_ref(v_a_1963_);
lean_inc(v_a_1962_);
lean_inc_ref(v_a_1961_);
v___x_1980_ = lean_apply_6(v_f_1959_, v_decl_1978_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, lean_box(0));
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; uint8_t v___x_1982_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
v___x_1982_ = lean_unbox(v_a_1981_);
lean_dec(v_a_1981_);
if (v___x_1982_ == 0)
{
lean_object* v_value_1983_; lean_object* v___x_1984_; 
lean_dec_ref_known(v___x_1980_, 1);
v_value_1983_ = lean_ctor_get(v_decl_1978_, 4);
lean_inc_ref(v_value_1983_);
lean_dec_ref(v_decl_1978_);
lean_inc_ref(v_f_1959_);
v___x_1984_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_1958_, v_f_1959_, v_value_1983_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; uint8_t v___x_1986_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
v___x_1986_ = lean_unbox(v_a_1985_);
lean_dec(v_a_1985_);
if (v___x_1986_ == 0)
{
lean_dec_ref_known(v___x_1984_, 1);
v_a_1960_ = v_k_1979_;
goto _start;
}
else
{
lean_dec_ref(v_k_1979_);
lean_dec_ref(v_f_1959_);
return v___x_1984_;
}
}
else
{
lean_dec_ref(v_k_1979_);
lean_dec_ref(v_f_1959_);
return v___x_1984_;
}
}
else
{
lean_dec_ref(v_k_1979_);
lean_dec_ref(v_decl_1978_);
lean_dec_ref(v_f_1959_);
return v___x_1980_;
}
}
else
{
lean_dec_ref(v_k_1979_);
lean_dec_ref(v_decl_1978_);
lean_dec_ref(v_f_1959_);
return v___x_1980_;
}
}
case 4:
{
lean_object* v_cases_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2007_; 
v_cases_1988_ = lean_ctor_get(v_a_1960_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_a_1960_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1990_ = v_a_1960_;
v_isShared_1991_ = v_isSharedCheck_2007_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_cases_1988_);
lean_dec(v_a_1960_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2007_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v_alts_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v_alts_1992_ = lean_ctor_get(v_cases_1988_, 3);
lean_inc_ref(v_alts_1992_);
lean_dec_ref(v_cases_1988_);
v___x_1993_ = lean_unsigned_to_nat(0u);
v___x_1994_ = lean_array_get_size(v_alts_1992_);
v___x_1995_ = lean_nat_dec_lt(v___x_1993_, v___x_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; lean_object* v___x_1998_; 
lean_dec_ref(v_alts_1992_);
lean_dec_ref(v_f_1959_);
v___x_1996_ = lean_box(v___x_1995_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set_tag(v___x_1990_, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1996_);
v___x_1998_ = v___x_1990_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
else
{
if (v___x_1995_ == 0)
{
lean_object* v___x_2000_; lean_object* v___x_2002_; 
lean_dec_ref(v_alts_1992_);
lean_dec_ref(v_f_1959_);
v___x_2000_ = lean_box(v___x_1995_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set_tag(v___x_1990_, 0);
lean_ctor_set(v___x_1990_, 0, v___x_2000_);
v___x_2002_ = v___x_1990_;
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
else
{
size_t v___x_2004_; size_t v___x_2005_; lean_object* v___x_2006_; 
lean_del_object(v___x_1990_);
v___x_2004_ = ((size_t)0ULL);
v___x_2005_ = lean_usize_of_nat(v___x_1994_);
v___x_2006_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(v_pu_1958_, v_f_1959_, v_alts_1992_, v___x_2004_, v___x_2005_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
lean_dec_ref(v_alts_1992_);
return v___x_2006_;
}
}
}
}
case 7:
{
lean_object* v_k_2008_; 
v_k_2008_ = lean_ctor_get(v_a_1960_, 3);
lean_inc_ref(v_k_2008_);
lean_dec_ref_known(v_a_1960_, 4);
v_a_1960_ = v_k_2008_;
goto _start;
}
case 8:
{
lean_object* v_k_2010_; 
v_k_2010_ = lean_ctor_get(v_a_1960_, 3);
lean_inc_ref(v_k_2010_);
lean_dec_ref_known(v_a_1960_, 4);
v_a_1960_ = v_k_2010_;
goto _start;
}
case 9:
{
lean_object* v_k_2012_; 
v_k_2012_ = lean_ctor_get(v_a_1960_, 5);
lean_inc_ref(v_k_2012_);
lean_dec_ref_known(v_a_1960_, 6);
v_a_1960_ = v_k_2012_;
goto _start;
}
case 10:
{
lean_object* v_k_2014_; 
v_k_2014_ = lean_ctor_get(v_a_1960_, 2);
lean_inc_ref(v_k_2014_);
lean_dec_ref_known(v_a_1960_, 3);
v_a_1960_ = v_k_2014_;
goto _start;
}
case 11:
{
lean_object* v_k_2016_; 
v_k_2016_ = lean_ctor_get(v_a_1960_, 2);
lean_inc_ref(v_k_2016_);
lean_dec_ref_known(v_a_1960_, 3);
v_a_1960_ = v_k_2016_;
goto _start;
}
case 12:
{
lean_object* v_k_2018_; 
v_k_2018_ = lean_ctor_get(v_a_1960_, 3);
lean_inc_ref(v_k_2018_);
lean_dec_ref_known(v_a_1960_, 4);
v_a_1960_ = v_k_2018_;
goto _start;
}
case 13:
{
lean_object* v_k_2020_; 
v_k_2020_ = lean_ctor_get(v_a_1960_, 1);
lean_inc_ref(v_k_2020_);
lean_dec_ref_known(v_a_1960_, 2);
v_a_1960_ = v_k_2020_;
goto _start;
}
default: 
{
uint8_t v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
lean_dec_ref(v_a_1960_);
lean_dec_ref(v_f_1959_);
v___x_2022_ = 0;
v___x_2023_ = lean_box(v___x_2022_);
v___x_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2023_);
return v___x_2024_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(uint8_t v_pu_2025_, lean_object* v_f_2026_, lean_object* v_as_2027_, size_t v_i_2028_, size_t v_stop_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
uint8_t v___x_2035_; 
v___x_2035_ = lean_usize_dec_eq(v_i_2028_, v_stop_2029_);
if (v___x_2035_ == 0)
{
uint8_t v___x_2036_; lean_object* v___y_2038_; lean_object* v___x_2053_; 
v___x_2036_ = 1;
v___x_2053_ = lean_array_uget_borrowed(v_as_2027_, v_i_2028_);
switch(lean_obj_tag(v___x_2053_))
{
case 0:
{
lean_object* v_code_2054_; 
v_code_2054_ = lean_ctor_get(v___x_2053_, 2);
lean_inc_ref(v_code_2054_);
v___y_2038_ = v_code_2054_;
goto v___jp_2037_;
}
case 1:
{
lean_object* v_code_2055_; 
v_code_2055_ = lean_ctor_get(v___x_2053_, 1);
lean_inc_ref(v_code_2055_);
v___y_2038_ = v_code_2055_;
goto v___jp_2037_;
}
default: 
{
lean_object* v_code_2056_; 
v_code_2056_ = lean_ctor_get(v___x_2053_, 0);
lean_inc_ref(v_code_2056_);
v___y_2038_ = v_code_2056_;
goto v___jp_2037_;
}
}
v___jp_2037_:
{
lean_object* v___x_2039_; 
lean_inc_ref(v_f_2026_);
v___x_2039_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_2025_, v_f_2026_, v___y_2038_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2052_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2052_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2052_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
uint8_t v___x_2044_; 
v___x_2044_ = lean_unbox(v_a_2040_);
lean_dec(v_a_2040_);
if (v___x_2044_ == 0)
{
size_t v___x_2045_; size_t v___x_2046_; 
lean_del_object(v___x_2042_);
v___x_2045_ = ((size_t)1ULL);
v___x_2046_ = lean_usize_add(v_i_2028_, v___x_2045_);
v_i_2028_ = v___x_2046_;
goto _start;
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2050_; 
lean_dec_ref(v_f_2026_);
v___x_2048_ = lean_box(v___x_2036_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2048_);
v___x_2050_ = v___x_2042_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
else
{
lean_dec_ref(v_f_2026_);
return v___x_2039_;
}
}
}
else
{
uint8_t v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_dec_ref(v_f_2026_);
v___x_2057_ = 0;
v___x_2058_ = lean_box(v___x_2057_);
v___x_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
return v___x_2059_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0___boxed(lean_object* v_pu_2060_, lean_object* v_f_2061_, lean_object* v_as_2062_, lean_object* v_i_2063_, lean_object* v_stop_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
uint8_t v_pu_boxed_2070_; size_t v_i_boxed_2071_; size_t v_stop_boxed_2072_; lean_object* v_res_2073_; 
v_pu_boxed_2070_ = lean_unbox(v_pu_2060_);
v_i_boxed_2071_ = lean_unbox_usize(v_i_2063_);
lean_dec(v_i_2063_);
v_stop_boxed_2072_ = lean_unbox_usize(v_stop_2064_);
lean_dec(v_stop_2064_);
v_res_2073_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(v_pu_boxed_2070_, v_f_2061_, v_as_2062_, v_i_boxed_2071_, v_stop_boxed_2072_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec_ref(v_as_2062_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go___boxed(lean_object* v_pu_2074_, lean_object* v_f_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_){
_start:
{
uint8_t v_pu_boxed_2082_; lean_object* v_res_2083_; 
v_pu_boxed_2082_ = lean_unbox(v_pu_2074_);
v_res_2083_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_boxed_2082_, v_f_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
lean_dec(v_a_2078_);
lean_dec_ref(v_a_2077_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(uint8_t v_pu_2084_, lean_object* v_f_2085_, lean_object* v_as_2086_, size_t v_i_2087_, size_t v_stop_2088_, lean_object* v_b_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v_a_2096_; uint8_t v___x_2100_; 
v___x_2100_ = lean_usize_dec_eq(v_i_2087_, v_stop_2088_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; lean_object* v_value_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2101_ = lean_array_uget_borrowed(v_as_2086_, v_i_2087_);
v_value_2102_ = lean_ctor_get(v___x_2101_, 1);
v___x_2103_ = lean_box(v_pu_2084_);
lean_inc_ref(v_f_2085_);
v___x_2104_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go___boxed), 8, 2);
lean_closure_set(v___x_2104_, 0, v___x_2103_);
lean_closure_set(v___x_2104_, 1, v_f_2085_);
lean_inc_ref(v_value_2102_);
v___x_2105_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2102_, v___x_2104_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; uint8_t v___x_2107_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2105_, 1);
v___x_2107_ = lean_unbox(v_a_2106_);
lean_dec(v_a_2106_);
if (v___x_2107_ == 0)
{
v_a_2096_ = v_b_2089_;
goto v___jp_2095_;
}
else
{
lean_object* v___x_2108_; 
lean_inc(v___x_2101_);
v___x_2108_ = lean_array_push(v_b_2089_, v___x_2101_);
v_a_2096_ = v___x_2108_;
goto v___jp_2095_;
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec_ref(v_b_2089_);
lean_dec_ref(v_f_2085_);
v_a_2109_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2105_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2105_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v___x_2117_; 
lean_dec_ref(v_f_2085_);
v___x_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2117_, 0, v_b_2089_);
return v___x_2117_;
}
v___jp_2095_:
{
size_t v___x_2097_; size_t v___x_2098_; 
v___x_2097_ = ((size_t)1ULL);
v___x_2098_ = lean_usize_add(v_i_2087_, v___x_2097_);
v_i_2087_ = v___x_2098_;
v_b_2089_ = v_a_2096_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0___boxed(lean_object* v_pu_2118_, lean_object* v_f_2119_, lean_object* v_as_2120_, lean_object* v_i_2121_, lean_object* v_stop_2122_, lean_object* v_b_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
uint8_t v_pu_boxed_2129_; size_t v_i_boxed_2130_; size_t v_stop_boxed_2131_; lean_object* v_res_2132_; 
v_pu_boxed_2129_ = lean_unbox(v_pu_2118_);
v_i_boxed_2130_ = lean_unbox_usize(v_i_2121_);
lean_dec(v_i_2121_);
v_stop_boxed_2131_ = lean_unbox_usize(v_stop_2122_);
lean_dec(v_stop_2122_);
v_res_2132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_boxed_2129_, v_f_2119_, v_as_2120_, v_i_boxed_2130_, v_stop_boxed_2131_, v_b_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec_ref(v_as_2120_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFunDecl(uint8_t v_pu_2133_, lean_object* v_f_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v___x_2141_ = lean_unsigned_to_nat(0u);
v___x_2142_ = lean_array_get_size(v_a_2135_);
v___x_2143_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2144_ = lean_nat_dec_lt(v___x_2141_, v___x_2142_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; 
lean_dec_ref(v_f_2134_);
v___x_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
return v___x_2145_;
}
else
{
size_t v___x_2146_; size_t v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = ((size_t)0ULL);
v___x_2147_ = lean_usize_of_nat(v___x_2142_);
v___x_2148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_2133_, v_f_2134_, v_a_2135_, v___x_2146_, v___x_2147_, v___x_2143_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_);
return v___x_2148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFunDecl___boxed(lean_object* v_pu_2149_, lean_object* v_f_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
uint8_t v_pu_boxed_2157_; lean_object* v_res_2158_; 
v_pu_boxed_2157_ = lean_unbox(v_pu_2149_);
v_res_2158_ = l_Lean_Compiler_LCNF_Probe_filterByFunDecl(v_pu_boxed_2157_, v_f_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
lean_dec(v_a_2155_);
lean_dec_ref(v_a_2154_);
lean_dec(v_a_2153_);
lean_dec_ref(v_a_2152_);
lean_dec_ref(v_a_2151_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(uint8_t v_pu_2159_, lean_object* v_f_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
switch(lean_obj_tag(v_a_2161_))
{
case 0:
{
lean_object* v_k_2167_; 
v_k_2167_ = lean_ctor_get(v_a_2161_, 1);
lean_inc_ref(v_k_2167_);
lean_dec_ref_known(v_a_2161_, 2);
v_a_2161_ = v_k_2167_;
goto _start;
}
case 1:
{
lean_object* v_decl_2169_; lean_object* v_k_2170_; lean_object* v_value_2171_; lean_object* v___x_2172_; 
v_decl_2169_ = lean_ctor_get(v_a_2161_, 0);
lean_inc_ref(v_decl_2169_);
v_k_2170_ = lean_ctor_get(v_a_2161_, 1);
lean_inc_ref(v_k_2170_);
lean_dec_ref_known(v_a_2161_, 2);
v_value_2171_ = lean_ctor_get(v_decl_2169_, 4);
lean_inc_ref(v_value_2171_);
lean_dec_ref(v_decl_2169_);
lean_inc_ref(v_f_2160_);
v___x_2172_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2159_, v_f_2160_, v_value_2171_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; uint8_t v___x_2174_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
v___x_2174_ = lean_unbox(v_a_2173_);
lean_dec(v_a_2173_);
if (v___x_2174_ == 0)
{
lean_dec_ref_known(v___x_2172_, 1);
v_a_2161_ = v_k_2170_;
goto _start;
}
else
{
lean_dec_ref(v_k_2170_);
lean_dec_ref(v_f_2160_);
return v___x_2172_;
}
}
else
{
lean_dec_ref(v_k_2170_);
lean_dec_ref(v_f_2160_);
return v___x_2172_;
}
}
case 2:
{
lean_object* v_decl_2176_; lean_object* v_k_2177_; lean_object* v_value_2178_; lean_object* v___x_2179_; 
v_decl_2176_ = lean_ctor_get(v_a_2161_, 0);
lean_inc_ref(v_decl_2176_);
v_k_2177_ = lean_ctor_get(v_a_2161_, 1);
lean_inc_ref(v_k_2177_);
lean_dec_ref_known(v_a_2161_, 2);
v_value_2178_ = lean_ctor_get(v_decl_2176_, 4);
lean_inc_ref(v_value_2178_);
lean_dec_ref(v_decl_2176_);
lean_inc_ref(v_f_2160_);
v___x_2179_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2159_, v_f_2160_, v_value_2178_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; uint8_t v___x_2181_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
v___x_2181_ = lean_unbox(v_a_2180_);
lean_dec(v_a_2180_);
if (v___x_2181_ == 0)
{
lean_dec_ref_known(v___x_2179_, 1);
v_a_2161_ = v_k_2177_;
goto _start;
}
else
{
lean_dec_ref(v_k_2177_);
lean_dec_ref(v_f_2160_);
return v___x_2179_;
}
}
else
{
lean_dec_ref(v_k_2177_);
lean_dec_ref(v_f_2160_);
return v___x_2179_;
}
}
case 4:
{
lean_object* v_cases_2183_; lean_object* v___x_2184_; 
v_cases_2183_ = lean_ctor_get(v_a_2161_, 0);
lean_inc_ref_n(v_cases_2183_, 2);
lean_dec_ref_known(v_a_2161_, 1);
lean_inc_ref(v_f_2160_);
lean_inc(v_a_2165_);
lean_inc_ref(v_a_2164_);
lean_inc(v_a_2163_);
lean_inc_ref(v_a_2162_);
v___x_2184_ = lean_apply_6(v_f_2160_, v_cases_2183_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, lean_box(0));
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; uint8_t v___x_2186_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
v___x_2186_ = lean_unbox(v_a_2185_);
lean_dec(v_a_2185_);
if (v___x_2186_ == 0)
{
lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2205_; 
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2205_ == 0)
{
lean_object* v_unused_2206_; 
v_unused_2206_ = lean_ctor_get(v___x_2184_, 0);
lean_dec(v_unused_2206_);
v___x_2188_ = v___x_2184_;
v_isShared_2189_ = v_isSharedCheck_2205_;
goto v_resetjp_2187_;
}
else
{
lean_dec(v___x_2184_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2205_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v_alts_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; uint8_t v___x_2193_; 
v_alts_2190_ = lean_ctor_get(v_cases_2183_, 3);
lean_inc_ref(v_alts_2190_);
lean_dec_ref(v_cases_2183_);
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = lean_array_get_size(v_alts_2190_);
v___x_2193_ = lean_nat_dec_lt(v___x_2191_, v___x_2192_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
lean_dec_ref(v_alts_2190_);
lean_dec_ref(v_f_2160_);
v___x_2194_ = lean_box(v___x_2193_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v___x_2194_);
v___x_2196_ = v___x_2188_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
else
{
if (v___x_2193_ == 0)
{
lean_object* v___x_2198_; lean_object* v___x_2200_; 
lean_dec_ref(v_alts_2190_);
lean_dec_ref(v_f_2160_);
v___x_2198_ = lean_box(v___x_2193_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v___x_2198_);
v___x_2200_ = v___x_2188_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
else
{
size_t v___x_2202_; size_t v___x_2203_; lean_object* v___x_2204_; 
lean_del_object(v___x_2188_);
v___x_2202_ = ((size_t)0ULL);
v___x_2203_ = lean_usize_of_nat(v___x_2192_);
v___x_2204_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(v_pu_2159_, v_f_2160_, v_alts_2190_, v___x_2202_, v___x_2203_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
lean_dec_ref(v_alts_2190_);
return v___x_2204_;
}
}
}
}
else
{
lean_dec_ref(v_cases_2183_);
lean_dec_ref(v_f_2160_);
return v___x_2184_;
}
}
else
{
lean_dec_ref(v_cases_2183_);
lean_dec_ref(v_f_2160_);
return v___x_2184_;
}
}
case 7:
{
lean_object* v_k_2207_; 
v_k_2207_ = lean_ctor_get(v_a_2161_, 3);
lean_inc_ref(v_k_2207_);
lean_dec_ref_known(v_a_2161_, 4);
v_a_2161_ = v_k_2207_;
goto _start;
}
case 8:
{
lean_object* v_k_2209_; 
v_k_2209_ = lean_ctor_get(v_a_2161_, 3);
lean_inc_ref(v_k_2209_);
lean_dec_ref_known(v_a_2161_, 4);
v_a_2161_ = v_k_2209_;
goto _start;
}
case 9:
{
lean_object* v_k_2211_; 
v_k_2211_ = lean_ctor_get(v_a_2161_, 5);
lean_inc_ref(v_k_2211_);
lean_dec_ref_known(v_a_2161_, 6);
v_a_2161_ = v_k_2211_;
goto _start;
}
case 10:
{
lean_object* v_k_2213_; 
v_k_2213_ = lean_ctor_get(v_a_2161_, 2);
lean_inc_ref(v_k_2213_);
lean_dec_ref_known(v_a_2161_, 3);
v_a_2161_ = v_k_2213_;
goto _start;
}
case 11:
{
lean_object* v_k_2215_; 
v_k_2215_ = lean_ctor_get(v_a_2161_, 2);
lean_inc_ref(v_k_2215_);
lean_dec_ref_known(v_a_2161_, 3);
v_a_2161_ = v_k_2215_;
goto _start;
}
case 12:
{
lean_object* v_k_2217_; 
v_k_2217_ = lean_ctor_get(v_a_2161_, 3);
lean_inc_ref(v_k_2217_);
lean_dec_ref_known(v_a_2161_, 4);
v_a_2161_ = v_k_2217_;
goto _start;
}
case 13:
{
lean_object* v_k_2219_; 
v_k_2219_ = lean_ctor_get(v_a_2161_, 1);
lean_inc_ref(v_k_2219_);
lean_dec_ref_known(v_a_2161_, 2);
v_a_2161_ = v_k_2219_;
goto _start;
}
default: 
{
uint8_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
lean_dec_ref(v_a_2161_);
lean_dec_ref(v_f_2160_);
v___x_2221_ = 0;
v___x_2222_ = lean_box(v___x_2221_);
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
return v___x_2223_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(uint8_t v_pu_2224_, lean_object* v_f_2225_, lean_object* v_as_2226_, size_t v_i_2227_, size_t v_stop_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
uint8_t v___x_2234_; 
v___x_2234_ = lean_usize_dec_eq(v_i_2227_, v_stop_2228_);
if (v___x_2234_ == 0)
{
uint8_t v___x_2235_; lean_object* v___y_2237_; lean_object* v___x_2252_; 
v___x_2235_ = 1;
v___x_2252_ = lean_array_uget_borrowed(v_as_2226_, v_i_2227_);
switch(lean_obj_tag(v___x_2252_))
{
case 0:
{
lean_object* v_code_2253_; 
v_code_2253_ = lean_ctor_get(v___x_2252_, 2);
lean_inc_ref(v_code_2253_);
v___y_2237_ = v_code_2253_;
goto v___jp_2236_;
}
case 1:
{
lean_object* v_code_2254_; 
v_code_2254_ = lean_ctor_get(v___x_2252_, 1);
lean_inc_ref(v_code_2254_);
v___y_2237_ = v_code_2254_;
goto v___jp_2236_;
}
default: 
{
lean_object* v_code_2255_; 
v_code_2255_ = lean_ctor_get(v___x_2252_, 0);
lean_inc_ref(v_code_2255_);
v___y_2237_ = v_code_2255_;
goto v___jp_2236_;
}
}
v___jp_2236_:
{
lean_object* v___x_2238_; 
lean_inc_ref(v_f_2225_);
v___x_2238_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2224_, v_f_2225_, v___y_2237_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2251_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2241_ = v___x_2238_;
v_isShared_2242_ = v_isSharedCheck_2251_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2238_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2251_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
uint8_t v___x_2243_; 
v___x_2243_ = lean_unbox(v_a_2239_);
lean_dec(v_a_2239_);
if (v___x_2243_ == 0)
{
size_t v___x_2244_; size_t v___x_2245_; 
lean_del_object(v___x_2241_);
v___x_2244_ = ((size_t)1ULL);
v___x_2245_ = lean_usize_add(v_i_2227_, v___x_2244_);
v_i_2227_ = v___x_2245_;
goto _start;
}
else
{
lean_object* v___x_2247_; lean_object* v___x_2249_; 
lean_dec_ref(v_f_2225_);
v___x_2247_ = lean_box(v___x_2235_);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v___x_2247_);
v___x_2249_ = v___x_2241_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2247_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
else
{
lean_dec_ref(v_f_2225_);
return v___x_2238_;
}
}
}
else
{
uint8_t v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
lean_dec_ref(v_f_2225_);
v___x_2256_ = 0;
v___x_2257_ = lean_box(v___x_2256_);
v___x_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
return v___x_2258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0___boxed(lean_object* v_pu_2259_, lean_object* v_f_2260_, lean_object* v_as_2261_, lean_object* v_i_2262_, lean_object* v_stop_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
uint8_t v_pu_boxed_2269_; size_t v_i_boxed_2270_; size_t v_stop_boxed_2271_; lean_object* v_res_2272_; 
v_pu_boxed_2269_ = lean_unbox(v_pu_2259_);
v_i_boxed_2270_ = lean_unbox_usize(v_i_2262_);
lean_dec(v_i_2262_);
v_stop_boxed_2271_ = lean_unbox_usize(v_stop_2263_);
lean_dec(v_stop_2263_);
v_res_2272_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(v_pu_boxed_2269_, v_f_2260_, v_as_2261_, v_i_boxed_2270_, v_stop_boxed_2271_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_as_2261_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go___boxed(lean_object* v_pu_2273_, lean_object* v_f_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
uint8_t v_pu_boxed_2281_; lean_object* v_res_2282_; 
v_pu_boxed_2281_ = lean_unbox(v_pu_2273_);
v_res_2282_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_boxed_2281_, v_f_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
lean_dec(v_a_2279_);
lean_dec_ref(v_a_2278_);
lean_dec(v_a_2277_);
lean_dec_ref(v_a_2276_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(uint8_t v_pu_2283_, lean_object* v_f_2284_, lean_object* v_as_2285_, size_t v_i_2286_, size_t v_stop_2287_, lean_object* v_b_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_a_2295_; uint8_t v___x_2299_; 
v___x_2299_ = lean_usize_dec_eq(v_i_2286_, v_stop_2287_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; lean_object* v_value_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2300_ = lean_array_uget_borrowed(v_as_2285_, v_i_2286_);
v_value_2301_ = lean_ctor_get(v___x_2300_, 1);
v___x_2302_ = lean_box(v_pu_2283_);
lean_inc_ref(v_f_2284_);
v___x_2303_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go___boxed), 8, 2);
lean_closure_set(v___x_2303_, 0, v___x_2302_);
lean_closure_set(v___x_2303_, 1, v_f_2284_);
lean_inc_ref(v_value_2301_);
v___x_2304_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2301_, v___x_2303_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; uint8_t v___x_2306_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2305_);
lean_dec_ref_known(v___x_2304_, 1);
v___x_2306_ = lean_unbox(v_a_2305_);
lean_dec(v_a_2305_);
if (v___x_2306_ == 0)
{
v_a_2295_ = v_b_2288_;
goto v___jp_2294_;
}
else
{
lean_object* v___x_2307_; 
lean_inc(v___x_2300_);
v___x_2307_ = lean_array_push(v_b_2288_, v___x_2300_);
v_a_2295_ = v___x_2307_;
goto v___jp_2294_;
}
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec_ref(v_b_2288_);
lean_dec_ref(v_f_2284_);
v_a_2308_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2304_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2304_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
else
{
lean_object* v___x_2316_; 
lean_dec_ref(v_f_2284_);
v___x_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2316_, 0, v_b_2288_);
return v___x_2316_;
}
v___jp_2294_:
{
size_t v___x_2296_; size_t v___x_2297_; 
v___x_2296_ = ((size_t)1ULL);
v___x_2297_ = lean_usize_add(v_i_2286_, v___x_2296_);
v_i_2286_ = v___x_2297_;
v_b_2288_ = v_a_2295_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0___boxed(lean_object* v_pu_2317_, lean_object* v_f_2318_, lean_object* v_as_2319_, lean_object* v_i_2320_, lean_object* v_stop_2321_, lean_object* v_b_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
uint8_t v_pu_boxed_2328_; size_t v_i_boxed_2329_; size_t v_stop_boxed_2330_; lean_object* v_res_2331_; 
v_pu_boxed_2328_ = lean_unbox(v_pu_2317_);
v_i_boxed_2329_ = lean_unbox_usize(v_i_2320_);
lean_dec(v_i_2320_);
v_stop_boxed_2330_ = lean_unbox_usize(v_stop_2321_);
lean_dec(v_stop_2321_);
v_res_2331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_boxed_2328_, v_f_2318_, v_as_2319_, v_i_boxed_2329_, v_stop_boxed_2330_, v_b_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec_ref(v_as_2319_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByCases(uint8_t v_pu_2332_, lean_object* v_f_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; 
v___x_2340_ = lean_unsigned_to_nat(0u);
v___x_2341_ = lean_array_get_size(v_a_2334_);
v___x_2342_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2343_ = lean_nat_dec_lt(v___x_2340_, v___x_2341_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; 
lean_dec_ref(v_f_2333_);
v___x_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2342_);
return v___x_2344_;
}
else
{
size_t v___x_2345_; size_t v___x_2346_; lean_object* v___x_2347_; 
v___x_2345_ = ((size_t)0ULL);
v___x_2346_ = lean_usize_of_nat(v___x_2341_);
v___x_2347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_2332_, v_f_2333_, v_a_2334_, v___x_2345_, v___x_2346_, v___x_2342_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_2347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByCases___boxed(lean_object* v_pu_2348_, lean_object* v_f_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_){
_start:
{
uint8_t v_pu_boxed_2356_; lean_object* v_res_2357_; 
v_pu_boxed_2356_ = lean_unbox(v_pu_2348_);
v_res_2357_ = l_Lean_Compiler_LCNF_Probe_filterByCases(v_pu_boxed_2356_, v_f_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
lean_dec(v_a_2354_);
lean_dec_ref(v_a_2353_);
lean_dec(v_a_2352_);
lean_dec_ref(v_a_2351_);
lean_dec_ref(v_a_2350_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(uint8_t v_pu_2358_, lean_object* v_f_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
switch(lean_obj_tag(v_a_2360_))
{
case 0:
{
lean_object* v_k_2366_; 
v_k_2366_ = lean_ctor_get(v_a_2360_, 1);
lean_inc_ref(v_k_2366_);
lean_dec_ref_known(v_a_2360_, 2);
v_a_2360_ = v_k_2366_;
goto _start;
}
case 1:
{
lean_object* v_decl_2368_; lean_object* v_k_2369_; lean_object* v_value_2370_; lean_object* v___x_2371_; 
v_decl_2368_ = lean_ctor_get(v_a_2360_, 0);
lean_inc_ref(v_decl_2368_);
v_k_2369_ = lean_ctor_get(v_a_2360_, 1);
lean_inc_ref(v_k_2369_);
lean_dec_ref_known(v_a_2360_, 2);
v_value_2370_ = lean_ctor_get(v_decl_2368_, 4);
lean_inc_ref(v_value_2370_);
lean_dec_ref(v_decl_2368_);
lean_inc_ref(v_f_2359_);
v___x_2371_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2358_, v_f_2359_, v_value_2370_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; uint8_t v___x_2373_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
v___x_2373_ = lean_unbox(v_a_2372_);
lean_dec(v_a_2372_);
if (v___x_2373_ == 0)
{
lean_dec_ref_known(v___x_2371_, 1);
v_a_2360_ = v_k_2369_;
goto _start;
}
else
{
lean_dec_ref(v_k_2369_);
lean_dec_ref(v_f_2359_);
return v___x_2371_;
}
}
else
{
lean_dec_ref(v_k_2369_);
lean_dec_ref(v_f_2359_);
return v___x_2371_;
}
}
case 2:
{
lean_object* v_decl_2375_; lean_object* v_k_2376_; lean_object* v_value_2377_; lean_object* v___x_2378_; 
v_decl_2375_ = lean_ctor_get(v_a_2360_, 0);
lean_inc_ref(v_decl_2375_);
v_k_2376_ = lean_ctor_get(v_a_2360_, 1);
lean_inc_ref(v_k_2376_);
lean_dec_ref_known(v_a_2360_, 2);
v_value_2377_ = lean_ctor_get(v_decl_2375_, 4);
lean_inc_ref(v_value_2377_);
lean_dec_ref(v_decl_2375_);
lean_inc_ref(v_f_2359_);
v___x_2378_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2358_, v_f_2359_, v_value_2377_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; uint8_t v___x_2380_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
v___x_2380_ = lean_unbox(v_a_2379_);
lean_dec(v_a_2379_);
if (v___x_2380_ == 0)
{
lean_dec_ref_known(v___x_2378_, 1);
v_a_2360_ = v_k_2376_;
goto _start;
}
else
{
lean_dec_ref(v_k_2376_);
lean_dec_ref(v_f_2359_);
return v___x_2378_;
}
}
else
{
lean_dec_ref(v_k_2376_);
lean_dec_ref(v_f_2359_);
return v___x_2378_;
}
}
case 3:
{
lean_object* v_fvarId_2382_; lean_object* v_args_2383_; lean_object* v___x_2384_; 
v_fvarId_2382_ = lean_ctor_get(v_a_2360_, 0);
lean_inc(v_fvarId_2382_);
v_args_2383_ = lean_ctor_get(v_a_2360_, 1);
lean_inc_ref(v_args_2383_);
lean_dec_ref_known(v_a_2360_, 2);
lean_inc(v_a_2364_);
lean_inc_ref(v_a_2363_);
lean_inc(v_a_2362_);
lean_inc_ref(v_a_2361_);
v___x_2384_ = lean_apply_7(v_f_2359_, v_fvarId_2382_, v_args_2383_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, lean_box(0));
return v___x_2384_;
}
case 4:
{
lean_object* v_cases_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2404_; 
v_cases_2385_ = lean_ctor_get(v_a_2360_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v_a_2360_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2387_ = v_a_2360_;
v_isShared_2388_ = v_isSharedCheck_2404_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_cases_2385_);
lean_dec(v_a_2360_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2404_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v_alts_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
v_alts_2389_ = lean_ctor_get(v_cases_2385_, 3);
lean_inc_ref(v_alts_2389_);
lean_dec_ref(v_cases_2385_);
v___x_2390_ = lean_unsigned_to_nat(0u);
v___x_2391_ = lean_array_get_size(v_alts_2389_);
v___x_2392_ = lean_nat_dec_lt(v___x_2390_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; lean_object* v___x_2395_; 
lean_dec_ref(v_alts_2389_);
lean_dec_ref(v_f_2359_);
v___x_2393_ = lean_box(v___x_2392_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set_tag(v___x_2387_, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2393_);
v___x_2395_ = v___x_2387_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
else
{
if (v___x_2392_ == 0)
{
lean_object* v___x_2397_; lean_object* v___x_2399_; 
lean_dec_ref(v_alts_2389_);
lean_dec_ref(v_f_2359_);
v___x_2397_ = lean_box(v___x_2392_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set_tag(v___x_2387_, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2397_);
v___x_2399_ = v___x_2387_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
else
{
size_t v___x_2401_; size_t v___x_2402_; lean_object* v___x_2403_; 
lean_del_object(v___x_2387_);
v___x_2401_ = ((size_t)0ULL);
v___x_2402_ = lean_usize_of_nat(v___x_2391_);
v___x_2403_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(v_pu_2358_, v_f_2359_, v_alts_2389_, v___x_2401_, v___x_2402_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
lean_dec_ref(v_alts_2389_);
return v___x_2403_;
}
}
}
}
case 7:
{
lean_object* v_k_2405_; 
v_k_2405_ = lean_ctor_get(v_a_2360_, 3);
lean_inc_ref(v_k_2405_);
lean_dec_ref_known(v_a_2360_, 4);
v_a_2360_ = v_k_2405_;
goto _start;
}
case 8:
{
lean_object* v_k_2407_; 
v_k_2407_ = lean_ctor_get(v_a_2360_, 3);
lean_inc_ref(v_k_2407_);
lean_dec_ref_known(v_a_2360_, 4);
v_a_2360_ = v_k_2407_;
goto _start;
}
case 9:
{
lean_object* v_k_2409_; 
v_k_2409_ = lean_ctor_get(v_a_2360_, 5);
lean_inc_ref(v_k_2409_);
lean_dec_ref_known(v_a_2360_, 6);
v_a_2360_ = v_k_2409_;
goto _start;
}
case 10:
{
lean_object* v_k_2411_; 
v_k_2411_ = lean_ctor_get(v_a_2360_, 2);
lean_inc_ref(v_k_2411_);
lean_dec_ref_known(v_a_2360_, 3);
v_a_2360_ = v_k_2411_;
goto _start;
}
case 11:
{
lean_object* v_k_2413_; 
v_k_2413_ = lean_ctor_get(v_a_2360_, 2);
lean_inc_ref(v_k_2413_);
lean_dec_ref_known(v_a_2360_, 3);
v_a_2360_ = v_k_2413_;
goto _start;
}
case 12:
{
lean_object* v_k_2415_; 
v_k_2415_ = lean_ctor_get(v_a_2360_, 3);
lean_inc_ref(v_k_2415_);
lean_dec_ref_known(v_a_2360_, 4);
v_a_2360_ = v_k_2415_;
goto _start;
}
case 13:
{
lean_object* v_k_2417_; 
v_k_2417_ = lean_ctor_get(v_a_2360_, 1);
lean_inc_ref(v_k_2417_);
lean_dec_ref_known(v_a_2360_, 2);
v_a_2360_ = v_k_2417_;
goto _start;
}
default: 
{
uint8_t v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
lean_dec_ref(v_a_2360_);
lean_dec_ref(v_f_2359_);
v___x_2419_ = 0;
v___x_2420_ = lean_box(v___x_2419_);
v___x_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2420_);
return v___x_2421_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(uint8_t v_pu_2422_, lean_object* v_f_2423_, lean_object* v_as_2424_, size_t v_i_2425_, size_t v_stop_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
uint8_t v___x_2432_; 
v___x_2432_ = lean_usize_dec_eq(v_i_2425_, v_stop_2426_);
if (v___x_2432_ == 0)
{
uint8_t v___x_2433_; lean_object* v___y_2435_; lean_object* v___x_2450_; 
v___x_2433_ = 1;
v___x_2450_ = lean_array_uget_borrowed(v_as_2424_, v_i_2425_);
switch(lean_obj_tag(v___x_2450_))
{
case 0:
{
lean_object* v_code_2451_; 
v_code_2451_ = lean_ctor_get(v___x_2450_, 2);
lean_inc_ref(v_code_2451_);
v___y_2435_ = v_code_2451_;
goto v___jp_2434_;
}
case 1:
{
lean_object* v_code_2452_; 
v_code_2452_ = lean_ctor_get(v___x_2450_, 1);
lean_inc_ref(v_code_2452_);
v___y_2435_ = v_code_2452_;
goto v___jp_2434_;
}
default: 
{
lean_object* v_code_2453_; 
v_code_2453_ = lean_ctor_get(v___x_2450_, 0);
lean_inc_ref(v_code_2453_);
v___y_2435_ = v_code_2453_;
goto v___jp_2434_;
}
}
v___jp_2434_:
{
lean_object* v___x_2436_; 
lean_inc_ref(v_f_2423_);
v___x_2436_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2422_, v_f_2423_, v___y_2435_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2449_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2439_ = v___x_2436_;
v_isShared_2440_ = v_isSharedCheck_2449_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2436_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2449_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
uint8_t v___x_2441_; 
v___x_2441_ = lean_unbox(v_a_2437_);
lean_dec(v_a_2437_);
if (v___x_2441_ == 0)
{
size_t v___x_2442_; size_t v___x_2443_; 
lean_del_object(v___x_2439_);
v___x_2442_ = ((size_t)1ULL);
v___x_2443_ = lean_usize_add(v_i_2425_, v___x_2442_);
v_i_2425_ = v___x_2443_;
goto _start;
}
else
{
lean_object* v___x_2445_; lean_object* v___x_2447_; 
lean_dec_ref(v_f_2423_);
v___x_2445_ = lean_box(v___x_2433_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2445_);
v___x_2447_ = v___x_2439_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
else
{
lean_dec_ref(v_f_2423_);
return v___x_2436_;
}
}
}
else
{
uint8_t v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
lean_dec_ref(v_f_2423_);
v___x_2454_ = 0;
v___x_2455_ = lean_box(v___x_2454_);
v___x_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
return v___x_2456_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0___boxed(lean_object* v_pu_2457_, lean_object* v_f_2458_, lean_object* v_as_2459_, lean_object* v_i_2460_, lean_object* v_stop_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
uint8_t v_pu_boxed_2467_; size_t v_i_boxed_2468_; size_t v_stop_boxed_2469_; lean_object* v_res_2470_; 
v_pu_boxed_2467_ = lean_unbox(v_pu_2457_);
v_i_boxed_2468_ = lean_unbox_usize(v_i_2460_);
lean_dec(v_i_2460_);
v_stop_boxed_2469_ = lean_unbox_usize(v_stop_2461_);
lean_dec(v_stop_2461_);
v_res_2470_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(v_pu_boxed_2467_, v_f_2458_, v_as_2459_, v_i_boxed_2468_, v_stop_boxed_2469_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec_ref(v_as_2459_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go___boxed(lean_object* v_pu_2471_, lean_object* v_f_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_){
_start:
{
uint8_t v_pu_boxed_2479_; lean_object* v_res_2480_; 
v_pu_boxed_2479_ = lean_unbox(v_pu_2471_);
v_res_2480_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_boxed_2479_, v_f_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
lean_dec(v_a_2477_);
lean_dec_ref(v_a_2476_);
lean_dec(v_a_2475_);
lean_dec_ref(v_a_2474_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(uint8_t v_pu_2481_, lean_object* v_f_2482_, lean_object* v_as_2483_, size_t v_i_2484_, size_t v_stop_2485_, lean_object* v_b_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_a_2493_; uint8_t v___x_2497_; 
v___x_2497_ = lean_usize_dec_eq(v_i_2484_, v_stop_2485_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; lean_object* v_value_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2498_ = lean_array_uget_borrowed(v_as_2483_, v_i_2484_);
v_value_2499_ = lean_ctor_get(v___x_2498_, 1);
v___x_2500_ = lean_box(v_pu_2481_);
lean_inc_ref(v_f_2482_);
v___x_2501_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go___boxed), 8, 2);
lean_closure_set(v___x_2501_, 0, v___x_2500_);
lean_closure_set(v___x_2501_, 1, v_f_2482_);
lean_inc_ref(v_value_2499_);
v___x_2502_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2499_, v___x_2501_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; uint8_t v___x_2504_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2503_);
lean_dec_ref_known(v___x_2502_, 1);
v___x_2504_ = lean_unbox(v_a_2503_);
lean_dec(v_a_2503_);
if (v___x_2504_ == 0)
{
v_a_2493_ = v_b_2486_;
goto v___jp_2492_;
}
else
{
lean_object* v___x_2505_; 
lean_inc(v___x_2498_);
v___x_2505_ = lean_array_push(v_b_2486_, v___x_2498_);
v_a_2493_ = v___x_2505_;
goto v___jp_2492_;
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec_ref(v_b_2486_);
lean_dec_ref(v_f_2482_);
v_a_2506_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2502_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2502_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
else
{
lean_object* v___x_2514_; 
lean_dec_ref(v_f_2482_);
v___x_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2514_, 0, v_b_2486_);
return v___x_2514_;
}
v___jp_2492_:
{
size_t v___x_2494_; size_t v___x_2495_; 
v___x_2494_ = ((size_t)1ULL);
v___x_2495_ = lean_usize_add(v_i_2484_, v___x_2494_);
v_i_2484_ = v___x_2495_;
v_b_2486_ = v_a_2493_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0___boxed(lean_object* v_pu_2515_, lean_object* v_f_2516_, lean_object* v_as_2517_, lean_object* v_i_2518_, lean_object* v_stop_2519_, lean_object* v_b_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
uint8_t v_pu_boxed_2526_; size_t v_i_boxed_2527_; size_t v_stop_boxed_2528_; lean_object* v_res_2529_; 
v_pu_boxed_2526_ = lean_unbox(v_pu_2515_);
v_i_boxed_2527_ = lean_unbox_usize(v_i_2518_);
lean_dec(v_i_2518_);
v_stop_boxed_2528_ = lean_unbox_usize(v_stop_2519_);
lean_dec(v_stop_2519_);
v_res_2529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_boxed_2526_, v_f_2516_, v_as_2517_, v_i_boxed_2527_, v_stop_boxed_2528_, v_b_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec_ref(v_as_2517_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJmp(uint8_t v_pu_2530_, lean_object* v_f_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; uint8_t v___x_2541_; 
v___x_2538_ = lean_unsigned_to_nat(0u);
v___x_2539_ = lean_array_get_size(v_a_2532_);
v___x_2540_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2541_ = lean_nat_dec_lt(v___x_2538_, v___x_2539_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; 
lean_dec_ref(v_f_2531_);
v___x_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2540_);
return v___x_2542_;
}
else
{
size_t v___x_2543_; size_t v___x_2544_; lean_object* v___x_2545_; 
v___x_2543_ = ((size_t)0ULL);
v___x_2544_ = lean_usize_of_nat(v___x_2539_);
v___x_2545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_2530_, v_f_2531_, v_a_2532_, v___x_2543_, v___x_2544_, v___x_2540_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
return v___x_2545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJmp___boxed(lean_object* v_pu_2546_, lean_object* v_f_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_){
_start:
{
uint8_t v_pu_boxed_2554_; lean_object* v_res_2555_; 
v_pu_boxed_2554_ = lean_unbox(v_pu_2546_);
v_res_2555_ = l_Lean_Compiler_LCNF_Probe_filterByJmp(v_pu_boxed_2554_, v_f_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
lean_dec_ref(v_a_2548_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(uint8_t v_pu_2556_, lean_object* v_f_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
switch(lean_obj_tag(v_a_2558_))
{
case 0:
{
lean_object* v_k_2564_; 
v_k_2564_ = lean_ctor_get(v_a_2558_, 1);
lean_inc_ref(v_k_2564_);
lean_dec_ref_known(v_a_2558_, 2);
v_a_2558_ = v_k_2564_;
goto _start;
}
case 1:
{
lean_object* v_decl_2566_; lean_object* v_k_2567_; lean_object* v_value_2568_; lean_object* v___x_2569_; 
v_decl_2566_ = lean_ctor_get(v_a_2558_, 0);
lean_inc_ref(v_decl_2566_);
v_k_2567_ = lean_ctor_get(v_a_2558_, 1);
lean_inc_ref(v_k_2567_);
lean_dec_ref_known(v_a_2558_, 2);
v_value_2568_ = lean_ctor_get(v_decl_2566_, 4);
lean_inc_ref(v_value_2568_);
lean_dec_ref(v_decl_2566_);
lean_inc_ref(v_f_2557_);
v___x_2569_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2556_, v_f_2557_, v_value_2568_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; uint8_t v___x_2571_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2570_);
v___x_2571_ = lean_unbox(v_a_2570_);
lean_dec(v_a_2570_);
if (v___x_2571_ == 0)
{
lean_dec_ref_known(v___x_2569_, 1);
v_a_2558_ = v_k_2567_;
goto _start;
}
else
{
lean_dec_ref(v_k_2567_);
lean_dec_ref(v_f_2557_);
return v___x_2569_;
}
}
else
{
lean_dec_ref(v_k_2567_);
lean_dec_ref(v_f_2557_);
return v___x_2569_;
}
}
case 2:
{
lean_object* v_decl_2573_; lean_object* v_k_2574_; lean_object* v_value_2575_; lean_object* v___x_2576_; 
v_decl_2573_ = lean_ctor_get(v_a_2558_, 0);
lean_inc_ref(v_decl_2573_);
v_k_2574_ = lean_ctor_get(v_a_2558_, 1);
lean_inc_ref(v_k_2574_);
lean_dec_ref_known(v_a_2558_, 2);
v_value_2575_ = lean_ctor_get(v_decl_2573_, 4);
lean_inc_ref(v_value_2575_);
lean_dec_ref(v_decl_2573_);
lean_inc_ref(v_f_2557_);
v___x_2576_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2556_, v_f_2557_, v_value_2575_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; uint8_t v___x_2578_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_a_2577_);
v___x_2578_ = lean_unbox(v_a_2577_);
lean_dec(v_a_2577_);
if (v___x_2578_ == 0)
{
lean_dec_ref_known(v___x_2576_, 1);
v_a_2558_ = v_k_2574_;
goto _start;
}
else
{
lean_dec_ref(v_k_2574_);
lean_dec_ref(v_f_2557_);
return v___x_2576_;
}
}
else
{
lean_dec_ref(v_k_2574_);
lean_dec_ref(v_f_2557_);
return v___x_2576_;
}
}
case 4:
{
lean_object* v_cases_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2599_; 
v_cases_2580_ = lean_ctor_get(v_a_2558_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v_a_2558_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2582_ = v_a_2558_;
v_isShared_2583_ = v_isSharedCheck_2599_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_cases_2580_);
lean_dec(v_a_2558_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2599_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v_alts_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; uint8_t v___x_2587_; 
v_alts_2584_ = lean_ctor_get(v_cases_2580_, 3);
lean_inc_ref(v_alts_2584_);
lean_dec_ref(v_cases_2580_);
v___x_2585_ = lean_unsigned_to_nat(0u);
v___x_2586_ = lean_array_get_size(v_alts_2584_);
v___x_2587_ = lean_nat_dec_lt(v___x_2585_, v___x_2586_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2588_; lean_object* v___x_2590_; 
lean_dec_ref(v_alts_2584_);
lean_dec_ref(v_f_2557_);
v___x_2588_ = lean_box(v___x_2587_);
if (v_isShared_2583_ == 0)
{
lean_ctor_set_tag(v___x_2582_, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2588_);
v___x_2590_ = v___x_2582_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
else
{
if (v___x_2587_ == 0)
{
lean_object* v___x_2592_; lean_object* v___x_2594_; 
lean_dec_ref(v_alts_2584_);
lean_dec_ref(v_f_2557_);
v___x_2592_ = lean_box(v___x_2587_);
if (v_isShared_2583_ == 0)
{
lean_ctor_set_tag(v___x_2582_, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2592_);
v___x_2594_ = v___x_2582_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
else
{
size_t v___x_2596_; size_t v___x_2597_; lean_object* v___x_2598_; 
lean_del_object(v___x_2582_);
v___x_2596_ = ((size_t)0ULL);
v___x_2597_ = lean_usize_of_nat(v___x_2586_);
v___x_2598_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(v_pu_2556_, v_f_2557_, v_alts_2584_, v___x_2596_, v___x_2597_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
lean_dec_ref(v_alts_2584_);
return v___x_2598_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_2600_; lean_object* v___x_2601_; 
v_fvarId_2600_ = lean_ctor_get(v_a_2558_, 0);
lean_inc(v_fvarId_2600_);
lean_dec_ref_known(v_a_2558_, 1);
lean_inc(v_a_2562_);
lean_inc_ref(v_a_2561_);
lean_inc(v_a_2560_);
lean_inc_ref(v_a_2559_);
v___x_2601_ = lean_apply_6(v_f_2557_, v_fvarId_2600_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, lean_box(0));
return v___x_2601_;
}
case 7:
{
lean_object* v_k_2602_; 
v_k_2602_ = lean_ctor_get(v_a_2558_, 3);
lean_inc_ref(v_k_2602_);
lean_dec_ref_known(v_a_2558_, 4);
v_a_2558_ = v_k_2602_;
goto _start;
}
case 8:
{
lean_object* v_k_2604_; 
v_k_2604_ = lean_ctor_get(v_a_2558_, 3);
lean_inc_ref(v_k_2604_);
lean_dec_ref_known(v_a_2558_, 4);
v_a_2558_ = v_k_2604_;
goto _start;
}
case 9:
{
lean_object* v_k_2606_; 
v_k_2606_ = lean_ctor_get(v_a_2558_, 5);
lean_inc_ref(v_k_2606_);
lean_dec_ref_known(v_a_2558_, 6);
v_a_2558_ = v_k_2606_;
goto _start;
}
case 10:
{
lean_object* v_k_2608_; 
v_k_2608_ = lean_ctor_get(v_a_2558_, 2);
lean_inc_ref(v_k_2608_);
lean_dec_ref_known(v_a_2558_, 3);
v_a_2558_ = v_k_2608_;
goto _start;
}
case 11:
{
lean_object* v_k_2610_; 
v_k_2610_ = lean_ctor_get(v_a_2558_, 2);
lean_inc_ref(v_k_2610_);
lean_dec_ref_known(v_a_2558_, 3);
v_a_2558_ = v_k_2610_;
goto _start;
}
case 12:
{
lean_object* v_k_2612_; 
v_k_2612_ = lean_ctor_get(v_a_2558_, 3);
lean_inc_ref(v_k_2612_);
lean_dec_ref_known(v_a_2558_, 4);
v_a_2558_ = v_k_2612_;
goto _start;
}
case 13:
{
lean_object* v_k_2614_; 
v_k_2614_ = lean_ctor_get(v_a_2558_, 1);
lean_inc_ref(v_k_2614_);
lean_dec_ref_known(v_a_2558_, 2);
v_a_2558_ = v_k_2614_;
goto _start;
}
default: 
{
uint8_t v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
lean_dec_ref(v_a_2558_);
lean_dec_ref(v_f_2557_);
v___x_2616_ = 0;
v___x_2617_ = lean_box(v___x_2616_);
v___x_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
return v___x_2618_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(uint8_t v_pu_2619_, lean_object* v_f_2620_, lean_object* v_as_2621_, size_t v_i_2622_, size_t v_stop_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
uint8_t v___x_2629_; 
v___x_2629_ = lean_usize_dec_eq(v_i_2622_, v_stop_2623_);
if (v___x_2629_ == 0)
{
uint8_t v___x_2630_; lean_object* v___y_2632_; lean_object* v___x_2647_; 
v___x_2630_ = 1;
v___x_2647_ = lean_array_uget_borrowed(v_as_2621_, v_i_2622_);
switch(lean_obj_tag(v___x_2647_))
{
case 0:
{
lean_object* v_code_2648_; 
v_code_2648_ = lean_ctor_get(v___x_2647_, 2);
lean_inc_ref(v_code_2648_);
v___y_2632_ = v_code_2648_;
goto v___jp_2631_;
}
case 1:
{
lean_object* v_code_2649_; 
v_code_2649_ = lean_ctor_get(v___x_2647_, 1);
lean_inc_ref(v_code_2649_);
v___y_2632_ = v_code_2649_;
goto v___jp_2631_;
}
default: 
{
lean_object* v_code_2650_; 
v_code_2650_ = lean_ctor_get(v___x_2647_, 0);
lean_inc_ref(v_code_2650_);
v___y_2632_ = v_code_2650_;
goto v___jp_2631_;
}
}
v___jp_2631_:
{
lean_object* v___x_2633_; 
lean_inc_ref(v_f_2620_);
v___x_2633_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2619_, v_f_2620_, v___y_2632_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2646_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2636_ = v___x_2633_;
v_isShared_2637_ = v_isSharedCheck_2646_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2633_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2646_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
uint8_t v___x_2638_; 
v___x_2638_ = lean_unbox(v_a_2634_);
lean_dec(v_a_2634_);
if (v___x_2638_ == 0)
{
size_t v___x_2639_; size_t v___x_2640_; 
lean_del_object(v___x_2636_);
v___x_2639_ = ((size_t)1ULL);
v___x_2640_ = lean_usize_add(v_i_2622_, v___x_2639_);
v_i_2622_ = v___x_2640_;
goto _start;
}
else
{
lean_object* v___x_2642_; lean_object* v___x_2644_; 
lean_dec_ref(v_f_2620_);
v___x_2642_ = lean_box(v___x_2630_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 0, v___x_2642_);
v___x_2644_ = v___x_2636_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2642_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
else
{
lean_dec_ref(v_f_2620_);
return v___x_2633_;
}
}
}
else
{
uint8_t v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
lean_dec_ref(v_f_2620_);
v___x_2651_ = 0;
v___x_2652_ = lean_box(v___x_2651_);
v___x_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
return v___x_2653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0___boxed(lean_object* v_pu_2654_, lean_object* v_f_2655_, lean_object* v_as_2656_, lean_object* v_i_2657_, lean_object* v_stop_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
uint8_t v_pu_boxed_2664_; size_t v_i_boxed_2665_; size_t v_stop_boxed_2666_; lean_object* v_res_2667_; 
v_pu_boxed_2664_ = lean_unbox(v_pu_2654_);
v_i_boxed_2665_ = lean_unbox_usize(v_i_2657_);
lean_dec(v_i_2657_);
v_stop_boxed_2666_ = lean_unbox_usize(v_stop_2658_);
lean_dec(v_stop_2658_);
v_res_2667_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(v_pu_boxed_2664_, v_f_2655_, v_as_2656_, v_i_boxed_2665_, v_stop_boxed_2666_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec_ref(v_as_2656_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go___boxed(lean_object* v_pu_2668_, lean_object* v_f_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
uint8_t v_pu_boxed_2676_; lean_object* v_res_2677_; 
v_pu_boxed_2676_ = lean_unbox(v_pu_2668_);
v_res_2677_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_boxed_2676_, v_f_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
lean_dec(v_a_2674_);
lean_dec_ref(v_a_2673_);
lean_dec(v_a_2672_);
lean_dec_ref(v_a_2671_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(uint8_t v_pu_2678_, lean_object* v_f_2679_, lean_object* v_as_2680_, size_t v_i_2681_, size_t v_stop_2682_, lean_object* v_b_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_a_2690_; uint8_t v___x_2694_; 
v___x_2694_ = lean_usize_dec_eq(v_i_2681_, v_stop_2682_);
if (v___x_2694_ == 0)
{
lean_object* v___x_2695_; lean_object* v_value_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2695_ = lean_array_uget_borrowed(v_as_2680_, v_i_2681_);
v_value_2696_ = lean_ctor_get(v___x_2695_, 1);
v___x_2697_ = lean_box(v_pu_2678_);
lean_inc_ref(v_f_2679_);
v___x_2698_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go___boxed), 8, 2);
lean_closure_set(v___x_2698_, 0, v___x_2697_);
lean_closure_set(v___x_2698_, 1, v_f_2679_);
lean_inc_ref(v_value_2696_);
v___x_2699_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2696_, v___x_2698_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; uint8_t v___x_2701_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2700_);
lean_dec_ref_known(v___x_2699_, 1);
v___x_2701_ = lean_unbox(v_a_2700_);
lean_dec(v_a_2700_);
if (v___x_2701_ == 0)
{
v_a_2690_ = v_b_2683_;
goto v___jp_2689_;
}
else
{
lean_object* v___x_2702_; 
lean_inc(v___x_2695_);
v___x_2702_ = lean_array_push(v_b_2683_, v___x_2695_);
v_a_2690_ = v___x_2702_;
goto v___jp_2689_;
}
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec_ref(v_b_2683_);
lean_dec_ref(v_f_2679_);
v_a_2703_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2699_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2699_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
else
{
lean_object* v___x_2711_; 
lean_dec_ref(v_f_2679_);
v___x_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2711_, 0, v_b_2683_);
return v___x_2711_;
}
v___jp_2689_:
{
size_t v___x_2691_; size_t v___x_2692_; 
v___x_2691_ = ((size_t)1ULL);
v___x_2692_ = lean_usize_add(v_i_2681_, v___x_2691_);
v_i_2681_ = v___x_2692_;
v_b_2683_ = v_a_2690_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0___boxed(lean_object* v_pu_2712_, lean_object* v_f_2713_, lean_object* v_as_2714_, lean_object* v_i_2715_, lean_object* v_stop_2716_, lean_object* v_b_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
uint8_t v_pu_boxed_2723_; size_t v_i_boxed_2724_; size_t v_stop_boxed_2725_; lean_object* v_res_2726_; 
v_pu_boxed_2723_ = lean_unbox(v_pu_2712_);
v_i_boxed_2724_ = lean_unbox_usize(v_i_2715_);
lean_dec(v_i_2715_);
v_stop_boxed_2725_ = lean_unbox_usize(v_stop_2716_);
lean_dec(v_stop_2716_);
v_res_2726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_boxed_2723_, v_f_2713_, v_as_2714_, v_i_boxed_2724_, v_stop_boxed_2725_, v_b_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec_ref(v_as_2714_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByReturn(uint8_t v_pu_2727_, lean_object* v_f_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; uint8_t v___x_2738_; 
v___x_2735_ = lean_unsigned_to_nat(0u);
v___x_2736_ = lean_array_get_size(v_a_2729_);
v___x_2737_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2738_ = lean_nat_dec_lt(v___x_2735_, v___x_2736_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; 
lean_dec_ref(v_f_2728_);
v___x_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2737_);
return v___x_2739_;
}
else
{
size_t v___x_2740_; size_t v___x_2741_; lean_object* v___x_2742_; 
v___x_2740_ = ((size_t)0ULL);
v___x_2741_ = lean_usize_of_nat(v___x_2736_);
v___x_2742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_2727_, v_f_2728_, v_a_2729_, v___x_2740_, v___x_2741_, v___x_2737_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_);
return v___x_2742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByReturn___boxed(lean_object* v_pu_2743_, lean_object* v_f_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_){
_start:
{
uint8_t v_pu_boxed_2751_; lean_object* v_res_2752_; 
v_pu_boxed_2751_ = lean_unbox(v_pu_2743_);
v_res_2752_ = l_Lean_Compiler_LCNF_Probe_filterByReturn(v_pu_boxed_2751_, v_f_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_);
lean_dec(v_a_2749_);
lean_dec_ref(v_a_2748_);
lean_dec(v_a_2747_);
lean_dec_ref(v_a_2746_);
lean_dec_ref(v_a_2745_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(uint8_t v_pu_2753_, lean_object* v_f_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_){
_start:
{
switch(lean_obj_tag(v_a_2755_))
{
case 0:
{
lean_object* v_k_2761_; 
v_k_2761_ = lean_ctor_get(v_a_2755_, 1);
lean_inc_ref(v_k_2761_);
lean_dec_ref_known(v_a_2755_, 2);
v_a_2755_ = v_k_2761_;
goto _start;
}
case 1:
{
lean_object* v_decl_2763_; lean_object* v_k_2764_; lean_object* v_value_2765_; lean_object* v___x_2766_; 
v_decl_2763_ = lean_ctor_get(v_a_2755_, 0);
lean_inc_ref(v_decl_2763_);
v_k_2764_ = lean_ctor_get(v_a_2755_, 1);
lean_inc_ref(v_k_2764_);
lean_dec_ref_known(v_a_2755_, 2);
v_value_2765_ = lean_ctor_get(v_decl_2763_, 4);
lean_inc_ref(v_value_2765_);
lean_dec_ref(v_decl_2763_);
lean_inc_ref(v_f_2754_);
v___x_2766_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2753_, v_f_2754_, v_value_2765_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; uint8_t v___x_2768_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
v___x_2768_ = lean_unbox(v_a_2767_);
lean_dec(v_a_2767_);
if (v___x_2768_ == 0)
{
lean_dec_ref_known(v___x_2766_, 1);
v_a_2755_ = v_k_2764_;
goto _start;
}
else
{
lean_dec_ref(v_k_2764_);
lean_dec_ref(v_f_2754_);
return v___x_2766_;
}
}
else
{
lean_dec_ref(v_k_2764_);
lean_dec_ref(v_f_2754_);
return v___x_2766_;
}
}
case 2:
{
lean_object* v_decl_2770_; lean_object* v_k_2771_; lean_object* v_value_2772_; lean_object* v___x_2773_; 
v_decl_2770_ = lean_ctor_get(v_a_2755_, 0);
lean_inc_ref(v_decl_2770_);
v_k_2771_ = lean_ctor_get(v_a_2755_, 1);
lean_inc_ref(v_k_2771_);
lean_dec_ref_known(v_a_2755_, 2);
v_value_2772_ = lean_ctor_get(v_decl_2770_, 4);
lean_inc_ref(v_value_2772_);
lean_dec_ref(v_decl_2770_);
lean_inc_ref(v_f_2754_);
v___x_2773_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2753_, v_f_2754_, v_value_2772_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; uint8_t v___x_2775_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
v___x_2775_ = lean_unbox(v_a_2774_);
lean_dec(v_a_2774_);
if (v___x_2775_ == 0)
{
lean_dec_ref_known(v___x_2773_, 1);
v_a_2755_ = v_k_2771_;
goto _start;
}
else
{
lean_dec_ref(v_k_2771_);
lean_dec_ref(v_f_2754_);
return v___x_2773_;
}
}
else
{
lean_dec_ref(v_k_2771_);
lean_dec_ref(v_f_2754_);
return v___x_2773_;
}
}
case 4:
{
lean_object* v_cases_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2796_; 
v_cases_2777_ = lean_ctor_get(v_a_2755_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v_a_2755_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2779_ = v_a_2755_;
v_isShared_2780_ = v_isSharedCheck_2796_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_cases_2777_);
lean_dec(v_a_2755_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2796_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v_alts_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v_alts_2781_ = lean_ctor_get(v_cases_2777_, 3);
lean_inc_ref(v_alts_2781_);
lean_dec_ref(v_cases_2777_);
v___x_2782_ = lean_unsigned_to_nat(0u);
v___x_2783_ = lean_array_get_size(v_alts_2781_);
v___x_2784_ = lean_nat_dec_lt(v___x_2782_, v___x_2783_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v___x_2787_; 
lean_dec_ref(v_alts_2781_);
lean_dec_ref(v_f_2754_);
v___x_2785_ = lean_box(v___x_2784_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set_tag(v___x_2779_, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2785_);
v___x_2787_ = v___x_2779_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
else
{
if (v___x_2784_ == 0)
{
lean_object* v___x_2789_; lean_object* v___x_2791_; 
lean_dec_ref(v_alts_2781_);
lean_dec_ref(v_f_2754_);
v___x_2789_ = lean_box(v___x_2784_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set_tag(v___x_2779_, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2789_);
v___x_2791_ = v___x_2779_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2789_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
else
{
size_t v___x_2793_; size_t v___x_2794_; lean_object* v___x_2795_; 
lean_del_object(v___x_2779_);
v___x_2793_ = ((size_t)0ULL);
v___x_2794_ = lean_usize_of_nat(v___x_2783_);
v___x_2795_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(v_pu_2753_, v_f_2754_, v_alts_2781_, v___x_2793_, v___x_2794_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_);
lean_dec_ref(v_alts_2781_);
return v___x_2795_;
}
}
}
}
case 6:
{
lean_object* v_type_2797_; lean_object* v___x_2798_; 
v_type_2797_ = lean_ctor_get(v_a_2755_, 0);
lean_inc_ref(v_type_2797_);
lean_dec_ref_known(v_a_2755_, 1);
lean_inc(v_a_2759_);
lean_inc_ref(v_a_2758_);
lean_inc(v_a_2757_);
lean_inc_ref(v_a_2756_);
v___x_2798_ = lean_apply_6(v_f_2754_, v_type_2797_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, lean_box(0));
return v___x_2798_;
}
case 7:
{
lean_object* v_k_2799_; 
v_k_2799_ = lean_ctor_get(v_a_2755_, 3);
lean_inc_ref(v_k_2799_);
lean_dec_ref_known(v_a_2755_, 4);
v_a_2755_ = v_k_2799_;
goto _start;
}
case 8:
{
lean_object* v_k_2801_; 
v_k_2801_ = lean_ctor_get(v_a_2755_, 3);
lean_inc_ref(v_k_2801_);
lean_dec_ref_known(v_a_2755_, 4);
v_a_2755_ = v_k_2801_;
goto _start;
}
case 9:
{
lean_object* v_k_2803_; 
v_k_2803_ = lean_ctor_get(v_a_2755_, 5);
lean_inc_ref(v_k_2803_);
lean_dec_ref_known(v_a_2755_, 6);
v_a_2755_ = v_k_2803_;
goto _start;
}
case 10:
{
lean_object* v_k_2805_; 
v_k_2805_ = lean_ctor_get(v_a_2755_, 2);
lean_inc_ref(v_k_2805_);
lean_dec_ref_known(v_a_2755_, 3);
v_a_2755_ = v_k_2805_;
goto _start;
}
case 11:
{
lean_object* v_k_2807_; 
v_k_2807_ = lean_ctor_get(v_a_2755_, 2);
lean_inc_ref(v_k_2807_);
lean_dec_ref_known(v_a_2755_, 3);
v_a_2755_ = v_k_2807_;
goto _start;
}
case 12:
{
lean_object* v_k_2809_; 
v_k_2809_ = lean_ctor_get(v_a_2755_, 3);
lean_inc_ref(v_k_2809_);
lean_dec_ref_known(v_a_2755_, 4);
v_a_2755_ = v_k_2809_;
goto _start;
}
case 13:
{
lean_object* v_k_2811_; 
v_k_2811_ = lean_ctor_get(v_a_2755_, 1);
lean_inc_ref(v_k_2811_);
lean_dec_ref_known(v_a_2755_, 2);
v_a_2755_ = v_k_2811_;
goto _start;
}
default: 
{
uint8_t v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
lean_dec_ref(v_a_2755_);
lean_dec_ref(v_f_2754_);
v___x_2813_ = 0;
v___x_2814_ = lean_box(v___x_2813_);
v___x_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
return v___x_2815_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(uint8_t v_pu_2816_, lean_object* v_f_2817_, lean_object* v_as_2818_, size_t v_i_2819_, size_t v_stop_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
uint8_t v___x_2826_; 
v___x_2826_ = lean_usize_dec_eq(v_i_2819_, v_stop_2820_);
if (v___x_2826_ == 0)
{
uint8_t v___x_2827_; lean_object* v___y_2829_; lean_object* v___x_2844_; 
v___x_2827_ = 1;
v___x_2844_ = lean_array_uget_borrowed(v_as_2818_, v_i_2819_);
switch(lean_obj_tag(v___x_2844_))
{
case 0:
{
lean_object* v_code_2845_; 
v_code_2845_ = lean_ctor_get(v___x_2844_, 2);
lean_inc_ref(v_code_2845_);
v___y_2829_ = v_code_2845_;
goto v___jp_2828_;
}
case 1:
{
lean_object* v_code_2846_; 
v_code_2846_ = lean_ctor_get(v___x_2844_, 1);
lean_inc_ref(v_code_2846_);
v___y_2829_ = v_code_2846_;
goto v___jp_2828_;
}
default: 
{
lean_object* v_code_2847_; 
v_code_2847_ = lean_ctor_get(v___x_2844_, 0);
lean_inc_ref(v_code_2847_);
v___y_2829_ = v_code_2847_;
goto v___jp_2828_;
}
}
v___jp_2828_:
{
lean_object* v___x_2830_; 
lean_inc_ref(v_f_2817_);
v___x_2830_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2816_, v_f_2817_, v___y_2829_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2843_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2833_ = v___x_2830_;
v_isShared_2834_ = v_isSharedCheck_2843_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2830_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2843_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
uint8_t v___x_2835_; 
v___x_2835_ = lean_unbox(v_a_2831_);
lean_dec(v_a_2831_);
if (v___x_2835_ == 0)
{
size_t v___x_2836_; size_t v___x_2837_; 
lean_del_object(v___x_2833_);
v___x_2836_ = ((size_t)1ULL);
v___x_2837_ = lean_usize_add(v_i_2819_, v___x_2836_);
v_i_2819_ = v___x_2837_;
goto _start;
}
else
{
lean_object* v___x_2839_; lean_object* v___x_2841_; 
lean_dec_ref(v_f_2817_);
v___x_2839_ = lean_box(v___x_2827_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 0, v___x_2839_);
v___x_2841_ = v___x_2833_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2839_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
}
else
{
lean_dec_ref(v_f_2817_);
return v___x_2830_;
}
}
}
else
{
uint8_t v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
lean_dec_ref(v_f_2817_);
v___x_2848_ = 0;
v___x_2849_ = lean_box(v___x_2848_);
v___x_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
return v___x_2850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0___boxed(lean_object* v_pu_2851_, lean_object* v_f_2852_, lean_object* v_as_2853_, lean_object* v_i_2854_, lean_object* v_stop_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
uint8_t v_pu_boxed_2861_; size_t v_i_boxed_2862_; size_t v_stop_boxed_2863_; lean_object* v_res_2864_; 
v_pu_boxed_2861_ = lean_unbox(v_pu_2851_);
v_i_boxed_2862_ = lean_unbox_usize(v_i_2854_);
lean_dec(v_i_2854_);
v_stop_boxed_2863_ = lean_unbox_usize(v_stop_2855_);
lean_dec(v_stop_2855_);
v_res_2864_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(v_pu_boxed_2861_, v_f_2852_, v_as_2853_, v_i_boxed_2862_, v_stop_boxed_2863_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec_ref(v_as_2853_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go___boxed(lean_object* v_pu_2865_, lean_object* v_f_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_){
_start:
{
uint8_t v_pu_boxed_2873_; lean_object* v_res_2874_; 
v_pu_boxed_2873_ = lean_unbox(v_pu_2865_);
v_res_2874_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_boxed_2873_, v_f_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_);
lean_dec(v_a_2871_);
lean_dec_ref(v_a_2870_);
lean_dec(v_a_2869_);
lean_dec_ref(v_a_2868_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(uint8_t v_pu_2875_, lean_object* v_f_2876_, lean_object* v_as_2877_, size_t v_i_2878_, size_t v_stop_2879_, lean_object* v_b_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v_a_2887_; uint8_t v___x_2891_; 
v___x_2891_ = lean_usize_dec_eq(v_i_2878_, v_stop_2879_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; lean_object* v_value_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2892_ = lean_array_uget_borrowed(v_as_2877_, v_i_2878_);
v_value_2893_ = lean_ctor_get(v___x_2892_, 1);
v___x_2894_ = lean_box(v_pu_2875_);
lean_inc_ref(v_f_2876_);
v___x_2895_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go___boxed), 8, 2);
lean_closure_set(v___x_2895_, 0, v___x_2894_);
lean_closure_set(v___x_2895_, 1, v_f_2876_);
lean_inc_ref(v_value_2893_);
v___x_2896_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2893_, v___x_2895_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; uint8_t v___x_2898_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_a_2897_);
lean_dec_ref_known(v___x_2896_, 1);
v___x_2898_ = lean_unbox(v_a_2897_);
lean_dec(v_a_2897_);
if (v___x_2898_ == 0)
{
v_a_2887_ = v_b_2880_;
goto v___jp_2886_;
}
else
{
lean_object* v___x_2899_; 
lean_inc(v___x_2892_);
v___x_2899_ = lean_array_push(v_b_2880_, v___x_2892_);
v_a_2887_ = v___x_2899_;
goto v___jp_2886_;
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec_ref(v_b_2880_);
lean_dec_ref(v_f_2876_);
v_a_2900_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2896_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2896_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
else
{
lean_object* v___x_2908_; 
lean_dec_ref(v_f_2876_);
v___x_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2908_, 0, v_b_2880_);
return v___x_2908_;
}
v___jp_2886_:
{
size_t v___x_2888_; size_t v___x_2889_; 
v___x_2888_ = ((size_t)1ULL);
v___x_2889_ = lean_usize_add(v_i_2878_, v___x_2888_);
v_i_2878_ = v___x_2889_;
v_b_2880_ = v_a_2887_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0___boxed(lean_object* v_pu_2909_, lean_object* v_f_2910_, lean_object* v_as_2911_, lean_object* v_i_2912_, lean_object* v_stop_2913_, lean_object* v_b_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
uint8_t v_pu_boxed_2920_; size_t v_i_boxed_2921_; size_t v_stop_boxed_2922_; lean_object* v_res_2923_; 
v_pu_boxed_2920_ = lean_unbox(v_pu_2909_);
v_i_boxed_2921_ = lean_unbox_usize(v_i_2912_);
lean_dec(v_i_2912_);
v_stop_boxed_2922_ = lean_unbox_usize(v_stop_2913_);
lean_dec(v_stop_2913_);
v_res_2923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_boxed_2920_, v_f_2910_, v_as_2911_, v_i_boxed_2921_, v_stop_boxed_2922_, v_b_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec_ref(v_as_2911_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByUnreach(uint8_t v_pu_2924_, lean_object* v_f_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; uint8_t v___x_2935_; 
v___x_2932_ = lean_unsigned_to_nat(0u);
v___x_2933_ = lean_array_get_size(v_a_2926_);
v___x_2934_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2935_ = lean_nat_dec_lt(v___x_2932_, v___x_2933_);
if (v___x_2935_ == 0)
{
lean_object* v___x_2936_; 
lean_dec_ref(v_f_2925_);
v___x_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2934_);
return v___x_2936_;
}
else
{
size_t v___x_2937_; size_t v___x_2938_; lean_object* v___x_2939_; 
v___x_2937_ = ((size_t)0ULL);
v___x_2938_ = lean_usize_of_nat(v___x_2933_);
v___x_2939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_2924_, v_f_2925_, v_a_2926_, v___x_2937_, v___x_2938_, v___x_2934_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_);
return v___x_2939_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByUnreach___boxed(lean_object* v_pu_2940_, lean_object* v_f_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
uint8_t v_pu_boxed_2948_; lean_object* v_res_2949_; 
v_pu_boxed_2948_ = lean_unbox(v_pu_2940_);
v_res_2949_ = l_Lean_Compiler_LCNF_Probe_filterByUnreach(v_pu_boxed_2948_, v_f_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
lean_dec_ref(v_a_2942_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0(lean_object* v_decl_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v_toSignature_2956_; lean_object* v_name_2957_; lean_object* v___x_2958_; 
v_toSignature_2956_ = lean_ctor_get(v_decl_2950_, 0);
v_name_2957_ = lean_ctor_get(v_toSignature_2956_, 0);
lean_inc(v_name_2957_);
v___x_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2958_, 0, v_name_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0___boxed(lean_object* v_decl_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0(v_decl_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec_ref(v_decl_2959_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg(lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_){
_start:
{
lean_object* v___x_2973_; lean_object* v_toApplicative_2974_; lean_object* v_toFunctor_2975_; lean_object* v_toSeq_2976_; lean_object* v_toSeqLeft_2977_; lean_object* v_toSeqRight_2978_; lean_object* v___f_2979_; lean_object* v___f_2980_; lean_object* v___f_2981_; lean_object* v___f_2982_; lean_object* v___x_2983_; lean_object* v___f_2984_; lean_object* v___f_2985_; lean_object* v___f_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v_toApplicative_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3022_; 
v___x_2973_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_2974_ = lean_ctor_get(v___x_2973_, 0);
v_toFunctor_2975_ = lean_ctor_get(v_toApplicative_2974_, 0);
v_toSeq_2976_ = lean_ctor_get(v_toApplicative_2974_, 2);
v_toSeqLeft_2977_ = lean_ctor_get(v_toApplicative_2974_, 3);
v_toSeqRight_2978_ = lean_ctor_get(v_toApplicative_2974_, 4);
v___f_2979_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_2980_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2975_, 2);
v___f_2981_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2981_, 0, v_toFunctor_2975_);
v___f_2982_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2982_, 0, v_toFunctor_2975_);
v___x_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___f_2981_);
lean_ctor_set(v___x_2983_, 1, v___f_2982_);
lean_inc(v_toSeqRight_2978_);
v___f_2984_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2984_, 0, v_toSeqRight_2978_);
lean_inc(v_toSeqLeft_2977_);
v___f_2985_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2985_, 0, v_toSeqLeft_2977_);
lean_inc(v_toSeq_2976_);
v___f_2986_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2986_, 0, v_toSeq_2976_);
v___x_2987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2983_);
lean_ctor_set(v___x_2987_, 1, v___f_2979_);
lean_ctor_set(v___x_2987_, 2, v___f_2986_);
lean_ctor_set(v___x_2987_, 3, v___f_2985_);
lean_ctor_set(v___x_2987_, 4, v___f_2984_);
v___x_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
lean_ctor_set(v___x_2988_, 1, v___f_2980_);
v___x_2989_ = l_StateRefT_x27_instMonad___redArg(v___x_2988_);
v_toApplicative_2990_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3022_ == 0)
{
lean_object* v_unused_3023_; 
v_unused_3023_ = lean_ctor_get(v___x_2989_, 1);
lean_dec(v_unused_3023_);
v___x_2992_ = v___x_2989_;
v_isShared_2993_ = v_isSharedCheck_3022_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_toApplicative_2990_);
lean_dec(v___x_2989_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3022_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v_toFunctor_2994_; lean_object* v_toSeq_2995_; lean_object* v_toSeqLeft_2996_; lean_object* v_toSeqRight_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3020_; 
v_toFunctor_2994_ = lean_ctor_get(v_toApplicative_2990_, 0);
v_toSeq_2995_ = lean_ctor_get(v_toApplicative_2990_, 2);
v_toSeqLeft_2996_ = lean_ctor_get(v_toApplicative_2990_, 3);
v_toSeqRight_2997_ = lean_ctor_get(v_toApplicative_2990_, 4);
v_isSharedCheck_3020_ = !lean_is_exclusive(v_toApplicative_2990_);
if (v_isSharedCheck_3020_ == 0)
{
lean_object* v_unused_3021_; 
v_unused_3021_ = lean_ctor_get(v_toApplicative_2990_, 1);
lean_dec(v_unused_3021_);
v___x_2999_ = v_toApplicative_2990_;
v_isShared_3000_ = v_isSharedCheck_3020_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_toSeqRight_2997_);
lean_inc(v_toSeqLeft_2996_);
lean_inc(v_toSeq_2995_);
lean_inc(v_toFunctor_2994_);
lean_dec(v_toApplicative_2990_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3020_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___f_3001_; lean_object* v___f_3002_; lean_object* v___f_3003_; lean_object* v___f_3004_; lean_object* v___f_3005_; lean_object* v___x_3006_; lean_object* v___f_3007_; lean_object* v___f_3008_; lean_object* v___f_3009_; lean_object* v___x_3011_; 
v___f_3001_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0));
v___f_3002_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3003_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_2994_);
v___f_3004_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3004_, 0, v_toFunctor_2994_);
v___f_3005_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3005_, 0, v_toFunctor_2994_);
v___x_3006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3006_, 0, v___f_3004_);
lean_ctor_set(v___x_3006_, 1, v___f_3005_);
v___f_3007_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3007_, 0, v_toSeqRight_2997_);
v___f_3008_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3008_, 0, v_toSeqLeft_2996_);
v___f_3009_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3009_, 0, v_toSeq_2995_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 4, v___f_3007_);
lean_ctor_set(v___x_2999_, 3, v___f_3008_);
lean_ctor_set(v___x_2999_, 2, v___f_3009_);
lean_ctor_set(v___x_2999_, 1, v___f_3002_);
lean_ctor_set(v___x_2999_, 0, v___x_3006_);
v___x_3011_ = v___x_2999_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3006_);
lean_ctor_set(v_reuseFailAlloc_3019_, 1, v___f_3002_);
lean_ctor_set(v_reuseFailAlloc_3019_, 2, v___f_3009_);
lean_ctor_set(v_reuseFailAlloc_3019_, 3, v___f_3008_);
lean_ctor_set(v_reuseFailAlloc_3019_, 4, v___f_3007_);
v___x_3011_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
lean_object* v___x_3013_; 
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 1, v___f_3003_);
lean_ctor_set(v___x_2992_, 0, v___x_3011_);
v___x_3013_ = v___x_2992_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3011_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v___f_3003_);
v___x_3013_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
size_t v_sz_3014_; size_t v___x_3015_; lean_object* v___x_127__overap_3016_; lean_object* v___x_3017_; 
v_sz_3014_ = lean_array_size(v_a_2967_);
v___x_3015_ = ((size_t)0ULL);
v___x_127__overap_3016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3013_, v___f_3001_, v_sz_3014_, v___x_3015_, v_a_2967_);
lean_inc(v_a_2971_);
lean_inc_ref(v_a_2970_);
lean_inc(v_a_2969_);
lean_inc_ref(v_a_2968_);
v___x_3017_ = lean_apply_5(v___x_127__overap_3016_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, lean_box(0));
return v___x_3017_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___boxed(lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_Compiler_LCNF_Probe_declNames___redArg(v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_);
lean_dec(v_a_3028_);
lean_dec_ref(v_a_3027_);
lean_dec(v_a_3026_);
lean_dec_ref(v_a_3025_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames(uint8_t v_pu_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v___x_3038_; lean_object* v_toApplicative_3039_; lean_object* v_toFunctor_3040_; lean_object* v_toSeq_3041_; lean_object* v_toSeqLeft_3042_; lean_object* v_toSeqRight_3043_; lean_object* v___f_3044_; lean_object* v___f_3045_; lean_object* v___f_3046_; lean_object* v___f_3047_; lean_object* v___x_3048_; lean_object* v___f_3049_; lean_object* v___f_3050_; lean_object* v___f_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v_toApplicative_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3087_; 
v___x_3038_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3039_ = lean_ctor_get(v___x_3038_, 0);
v_toFunctor_3040_ = lean_ctor_get(v_toApplicative_3039_, 0);
v_toSeq_3041_ = lean_ctor_get(v_toApplicative_3039_, 2);
v_toSeqLeft_3042_ = lean_ctor_get(v_toApplicative_3039_, 3);
v_toSeqRight_3043_ = lean_ctor_get(v_toApplicative_3039_, 4);
v___f_3044_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3045_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3040_, 2);
v___f_3046_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3046_, 0, v_toFunctor_3040_);
v___f_3047_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3047_, 0, v_toFunctor_3040_);
v___x_3048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___f_3046_);
lean_ctor_set(v___x_3048_, 1, v___f_3047_);
lean_inc(v_toSeqRight_3043_);
v___f_3049_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3049_, 0, v_toSeqRight_3043_);
lean_inc(v_toSeqLeft_3042_);
v___f_3050_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3050_, 0, v_toSeqLeft_3042_);
lean_inc(v_toSeq_3041_);
v___f_3051_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3051_, 0, v_toSeq_3041_);
v___x_3052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3048_);
lean_ctor_set(v___x_3052_, 1, v___f_3044_);
lean_ctor_set(v___x_3052_, 2, v___f_3051_);
lean_ctor_set(v___x_3052_, 3, v___f_3050_);
lean_ctor_set(v___x_3052_, 4, v___f_3049_);
v___x_3053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
lean_ctor_set(v___x_3053_, 1, v___f_3045_);
v___x_3054_ = l_StateRefT_x27_instMonad___redArg(v___x_3053_);
v_toApplicative_3055_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3087_ == 0)
{
lean_object* v_unused_3088_; 
v_unused_3088_ = lean_ctor_get(v___x_3054_, 1);
lean_dec(v_unused_3088_);
v___x_3057_ = v___x_3054_;
v_isShared_3058_ = v_isSharedCheck_3087_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_toApplicative_3055_);
lean_dec(v___x_3054_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3087_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v_toFunctor_3059_; lean_object* v_toSeq_3060_; lean_object* v_toSeqLeft_3061_; lean_object* v_toSeqRight_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3085_; 
v_toFunctor_3059_ = lean_ctor_get(v_toApplicative_3055_, 0);
v_toSeq_3060_ = lean_ctor_get(v_toApplicative_3055_, 2);
v_toSeqLeft_3061_ = lean_ctor_get(v_toApplicative_3055_, 3);
v_toSeqRight_3062_ = lean_ctor_get(v_toApplicative_3055_, 4);
v_isSharedCheck_3085_ = !lean_is_exclusive(v_toApplicative_3055_);
if (v_isSharedCheck_3085_ == 0)
{
lean_object* v_unused_3086_; 
v_unused_3086_ = lean_ctor_get(v_toApplicative_3055_, 1);
lean_dec(v_unused_3086_);
v___x_3064_ = v_toApplicative_3055_;
v_isShared_3065_ = v_isSharedCheck_3085_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_toSeqRight_3062_);
lean_inc(v_toSeqLeft_3061_);
lean_inc(v_toSeq_3060_);
lean_inc(v_toFunctor_3059_);
lean_dec(v_toApplicative_3055_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3085_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___f_3066_; lean_object* v___f_3067_; lean_object* v___f_3068_; lean_object* v___f_3069_; lean_object* v___f_3070_; lean_object* v___x_3071_; lean_object* v___f_3072_; lean_object* v___f_3073_; lean_object* v___f_3074_; lean_object* v___x_3076_; 
v___f_3066_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0));
v___f_3067_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3068_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3059_);
v___f_3069_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3069_, 0, v_toFunctor_3059_);
v___f_3070_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3070_, 0, v_toFunctor_3059_);
v___x_3071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___f_3069_);
lean_ctor_set(v___x_3071_, 1, v___f_3070_);
v___f_3072_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3072_, 0, v_toSeqRight_3062_);
v___f_3073_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3073_, 0, v_toSeqLeft_3061_);
v___f_3074_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3074_, 0, v_toSeq_3060_);
if (v_isShared_3065_ == 0)
{
lean_ctor_set(v___x_3064_, 4, v___f_3072_);
lean_ctor_set(v___x_3064_, 3, v___f_3073_);
lean_ctor_set(v___x_3064_, 2, v___f_3074_);
lean_ctor_set(v___x_3064_, 1, v___f_3067_);
lean_ctor_set(v___x_3064_, 0, v___x_3071_);
v___x_3076_ = v___x_3064_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v___f_3067_);
lean_ctor_set(v_reuseFailAlloc_3084_, 2, v___f_3074_);
lean_ctor_set(v_reuseFailAlloc_3084_, 3, v___f_3073_);
lean_ctor_set(v_reuseFailAlloc_3084_, 4, v___f_3072_);
v___x_3076_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
lean_object* v___x_3078_; 
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 1, v___f_3068_);
lean_ctor_set(v___x_3057_, 0, v___x_3076_);
v___x_3078_ = v___x_3057_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3076_);
lean_ctor_set(v_reuseFailAlloc_3083_, 1, v___f_3068_);
v___x_3078_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
size_t v_sz_3079_; size_t v___x_3080_; lean_object* v___x_185__overap_3081_; lean_object* v___x_3082_; 
v_sz_3079_ = lean_array_size(v_a_3032_);
v___x_3080_ = ((size_t)0ULL);
v___x_185__overap_3081_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3078_, v___f_3066_, v_sz_3079_, v___x_3080_, v_a_3032_);
lean_inc(v_a_3036_);
lean_inc_ref(v_a_3035_);
lean_inc(v_a_3034_);
lean_inc_ref(v_a_3033_);
v___x_3082_ = lean_apply_5(v___x_185__overap_3081_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_, lean_box(0));
return v___x_3082_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___boxed(lean_object* v_pu_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_){
_start:
{
uint8_t v_pu_boxed_3096_; lean_object* v_res_3097_; 
v_pu_boxed_3096_ = lean_unbox(v_pu_3089_);
v_res_3097_ = l_Lean_Compiler_LCNF_Probe_declNames(v_pu_boxed_3096_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
lean_dec(v_a_3092_);
lean_dec_ref(v_a_3091_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0(lean_object* v_inst_3098_, lean_object* v_x_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3105_ = lean_apply_1(v_inst_3098_, v_x_3099_);
v___x_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed(lean_object* v_inst_3107_, lean_object* v_x_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0(v_inst_3107_, v_x_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg(lean_object* v_inst_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_){
_start:
{
lean_object* v___x_3122_; lean_object* v_toApplicative_3123_; lean_object* v_toFunctor_3124_; lean_object* v_toSeq_3125_; lean_object* v_toSeqLeft_3126_; lean_object* v_toSeqRight_3127_; lean_object* v___f_3128_; lean_object* v___f_3129_; lean_object* v___f_3130_; lean_object* v___f_3131_; lean_object* v___x_3132_; lean_object* v___f_3133_; lean_object* v___f_3134_; lean_object* v___f_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v_toApplicative_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3171_; 
v___x_3122_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3123_ = lean_ctor_get(v___x_3122_, 0);
v_toFunctor_3124_ = lean_ctor_get(v_toApplicative_3123_, 0);
v_toSeq_3125_ = lean_ctor_get(v_toApplicative_3123_, 2);
v_toSeqLeft_3126_ = lean_ctor_get(v_toApplicative_3123_, 3);
v_toSeqRight_3127_ = lean_ctor_get(v_toApplicative_3123_, 4);
v___f_3128_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3129_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3124_, 2);
v___f_3130_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3130_, 0, v_toFunctor_3124_);
v___f_3131_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3131_, 0, v_toFunctor_3124_);
v___x_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___f_3130_);
lean_ctor_set(v___x_3132_, 1, v___f_3131_);
lean_inc(v_toSeqRight_3127_);
v___f_3133_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3133_, 0, v_toSeqRight_3127_);
lean_inc(v_toSeqLeft_3126_);
v___f_3134_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3134_, 0, v_toSeqLeft_3126_);
lean_inc(v_toSeq_3125_);
v___f_3135_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3135_, 0, v_toSeq_3125_);
v___x_3136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3132_);
lean_ctor_set(v___x_3136_, 1, v___f_3128_);
lean_ctor_set(v___x_3136_, 2, v___f_3135_);
lean_ctor_set(v___x_3136_, 3, v___f_3134_);
lean_ctor_set(v___x_3136_, 4, v___f_3133_);
v___x_3137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
lean_ctor_set(v___x_3137_, 1, v___f_3129_);
v___x_3138_ = l_StateRefT_x27_instMonad___redArg(v___x_3137_);
v_toApplicative_3139_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3171_ == 0)
{
lean_object* v_unused_3172_; 
v_unused_3172_ = lean_ctor_get(v___x_3138_, 1);
lean_dec(v_unused_3172_);
v___x_3141_ = v___x_3138_;
v_isShared_3142_ = v_isSharedCheck_3171_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_toApplicative_3139_);
lean_dec(v___x_3138_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3171_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v_toFunctor_3143_; lean_object* v_toSeq_3144_; lean_object* v_toSeqLeft_3145_; lean_object* v_toSeqRight_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3169_; 
v_toFunctor_3143_ = lean_ctor_get(v_toApplicative_3139_, 0);
v_toSeq_3144_ = lean_ctor_get(v_toApplicative_3139_, 2);
v_toSeqLeft_3145_ = lean_ctor_get(v_toApplicative_3139_, 3);
v_toSeqRight_3146_ = lean_ctor_get(v_toApplicative_3139_, 4);
v_isSharedCheck_3169_ = !lean_is_exclusive(v_toApplicative_3139_);
if (v_isSharedCheck_3169_ == 0)
{
lean_object* v_unused_3170_; 
v_unused_3170_ = lean_ctor_get(v_toApplicative_3139_, 1);
lean_dec(v_unused_3170_);
v___x_3148_ = v_toApplicative_3139_;
v_isShared_3149_ = v_isSharedCheck_3169_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_toSeqRight_3146_);
lean_inc(v_toSeqLeft_3145_);
lean_inc(v_toSeq_3144_);
lean_inc(v_toFunctor_3143_);
lean_dec(v_toApplicative_3139_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3169_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___f_3150_; lean_object* v___f_3151_; lean_object* v___f_3152_; lean_object* v___f_3153_; lean_object* v___f_3154_; lean_object* v___x_3155_; lean_object* v___f_3156_; lean_object* v___f_3157_; lean_object* v___f_3158_; lean_object* v___x_3160_; 
v___f_3150_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3150_, 0, v_inst_3115_);
v___f_3151_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3152_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3143_);
v___f_3153_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3153_, 0, v_toFunctor_3143_);
v___f_3154_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3154_, 0, v_toFunctor_3143_);
v___x_3155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3155_, 0, v___f_3153_);
lean_ctor_set(v___x_3155_, 1, v___f_3154_);
v___f_3156_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3156_, 0, v_toSeqRight_3146_);
v___f_3157_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3157_, 0, v_toSeqLeft_3145_);
v___f_3158_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3158_, 0, v_toSeq_3144_);
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 4, v___f_3156_);
lean_ctor_set(v___x_3148_, 3, v___f_3157_);
lean_ctor_set(v___x_3148_, 2, v___f_3158_);
lean_ctor_set(v___x_3148_, 1, v___f_3151_);
lean_ctor_set(v___x_3148_, 0, v___x_3155_);
v___x_3160_ = v___x_3148_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3155_);
lean_ctor_set(v_reuseFailAlloc_3168_, 1, v___f_3151_);
lean_ctor_set(v_reuseFailAlloc_3168_, 2, v___f_3158_);
lean_ctor_set(v_reuseFailAlloc_3168_, 3, v___f_3157_);
lean_ctor_set(v_reuseFailAlloc_3168_, 4, v___f_3156_);
v___x_3160_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
lean_object* v___x_3162_; 
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 1, v___f_3152_);
lean_ctor_set(v___x_3141_, 0, v___x_3160_);
v___x_3162_ = v___x_3141_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v___x_3160_);
lean_ctor_set(v_reuseFailAlloc_3167_, 1, v___f_3152_);
v___x_3162_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
size_t v_sz_3163_; size_t v___x_3164_; lean_object* v___x_129__overap_3165_; lean_object* v___x_3166_; 
v_sz_3163_ = lean_array_size(v_a_3116_);
v___x_3164_ = ((size_t)0ULL);
v___x_129__overap_3165_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3162_, v___f_3150_, v_sz_3163_, v___x_3164_, v_a_3116_);
lean_inc(v_a_3120_);
lean_inc_ref(v_a_3119_);
lean_inc(v_a_3118_);
lean_inc_ref(v_a_3117_);
v___x_3166_ = lean_apply_5(v___x_129__overap_3165_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, lean_box(0));
return v___x_3166_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___boxed(lean_object* v_inst_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_){
_start:
{
lean_object* v_res_3180_; 
v_res_3180_ = l_Lean_Compiler_LCNF_Probe_toString___redArg(v_inst_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_);
lean_dec(v_a_3178_);
lean_dec_ref(v_a_3177_);
lean_dec(v_a_3176_);
lean_dec_ref(v_a_3175_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString(lean_object* v_00_u03b1_3181_, lean_object* v_inst_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v___x_3189_; lean_object* v_toApplicative_3190_; lean_object* v_toFunctor_3191_; lean_object* v_toSeq_3192_; lean_object* v_toSeqLeft_3193_; lean_object* v_toSeqRight_3194_; lean_object* v___f_3195_; lean_object* v___f_3196_; lean_object* v___f_3197_; lean_object* v___f_3198_; lean_object* v___x_3199_; lean_object* v___f_3200_; lean_object* v___f_3201_; lean_object* v___f_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v_toApplicative_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3238_; 
v___x_3189_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3190_ = lean_ctor_get(v___x_3189_, 0);
v_toFunctor_3191_ = lean_ctor_get(v_toApplicative_3190_, 0);
v_toSeq_3192_ = lean_ctor_get(v_toApplicative_3190_, 2);
v_toSeqLeft_3193_ = lean_ctor_get(v_toApplicative_3190_, 3);
v_toSeqRight_3194_ = lean_ctor_get(v_toApplicative_3190_, 4);
v___f_3195_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3196_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3191_, 2);
v___f_3197_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3197_, 0, v_toFunctor_3191_);
v___f_3198_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3198_, 0, v_toFunctor_3191_);
v___x_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3199_, 0, v___f_3197_);
lean_ctor_set(v___x_3199_, 1, v___f_3198_);
lean_inc(v_toSeqRight_3194_);
v___f_3200_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3200_, 0, v_toSeqRight_3194_);
lean_inc(v_toSeqLeft_3193_);
v___f_3201_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3201_, 0, v_toSeqLeft_3193_);
lean_inc(v_toSeq_3192_);
v___f_3202_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3202_, 0, v_toSeq_3192_);
v___x_3203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3199_);
lean_ctor_set(v___x_3203_, 1, v___f_3195_);
lean_ctor_set(v___x_3203_, 2, v___f_3202_);
lean_ctor_set(v___x_3203_, 3, v___f_3201_);
lean_ctor_set(v___x_3203_, 4, v___f_3200_);
v___x_3204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
lean_ctor_set(v___x_3204_, 1, v___f_3196_);
v___x_3205_ = l_StateRefT_x27_instMonad___redArg(v___x_3204_);
v_toApplicative_3206_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3238_ == 0)
{
lean_object* v_unused_3239_; 
v_unused_3239_ = lean_ctor_get(v___x_3205_, 1);
lean_dec(v_unused_3239_);
v___x_3208_ = v___x_3205_;
v_isShared_3209_ = v_isSharedCheck_3238_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_toApplicative_3206_);
lean_dec(v___x_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3238_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v_toFunctor_3210_; lean_object* v_toSeq_3211_; lean_object* v_toSeqLeft_3212_; lean_object* v_toSeqRight_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3236_; 
v_toFunctor_3210_ = lean_ctor_get(v_toApplicative_3206_, 0);
v_toSeq_3211_ = lean_ctor_get(v_toApplicative_3206_, 2);
v_toSeqLeft_3212_ = lean_ctor_get(v_toApplicative_3206_, 3);
v_toSeqRight_3213_ = lean_ctor_get(v_toApplicative_3206_, 4);
v_isSharedCheck_3236_ = !lean_is_exclusive(v_toApplicative_3206_);
if (v_isSharedCheck_3236_ == 0)
{
lean_object* v_unused_3237_; 
v_unused_3237_ = lean_ctor_get(v_toApplicative_3206_, 1);
lean_dec(v_unused_3237_);
v___x_3215_ = v_toApplicative_3206_;
v_isShared_3216_ = v_isSharedCheck_3236_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_toSeqRight_3213_);
lean_inc(v_toSeqLeft_3212_);
lean_inc(v_toSeq_3211_);
lean_inc(v_toFunctor_3210_);
lean_dec(v_toApplicative_3206_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3236_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___f_3217_; lean_object* v___f_3218_; lean_object* v___f_3219_; lean_object* v___f_3220_; lean_object* v___f_3221_; lean_object* v___x_3222_; lean_object* v___f_3223_; lean_object* v___f_3224_; lean_object* v___f_3225_; lean_object* v___x_3227_; 
v___f_3217_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3217_, 0, v_inst_3182_);
v___f_3218_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3219_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3210_);
v___f_3220_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3220_, 0, v_toFunctor_3210_);
v___f_3221_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3221_, 0, v_toFunctor_3210_);
v___x_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___f_3220_);
lean_ctor_set(v___x_3222_, 1, v___f_3221_);
v___f_3223_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3223_, 0, v_toSeqRight_3213_);
v___f_3224_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3224_, 0, v_toSeqLeft_3212_);
v___f_3225_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3225_, 0, v_toSeq_3211_);
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 4, v___f_3223_);
lean_ctor_set(v___x_3215_, 3, v___f_3224_);
lean_ctor_set(v___x_3215_, 2, v___f_3225_);
lean_ctor_set(v___x_3215_, 1, v___f_3218_);
lean_ctor_set(v___x_3215_, 0, v___x_3222_);
v___x_3227_ = v___x_3215_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3222_);
lean_ctor_set(v_reuseFailAlloc_3235_, 1, v___f_3218_);
lean_ctor_set(v_reuseFailAlloc_3235_, 2, v___f_3225_);
lean_ctor_set(v_reuseFailAlloc_3235_, 3, v___f_3224_);
lean_ctor_set(v_reuseFailAlloc_3235_, 4, v___f_3223_);
v___x_3227_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
lean_object* v___x_3229_; 
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 1, v___f_3219_);
lean_ctor_set(v___x_3208_, 0, v___x_3227_);
v___x_3229_ = v___x_3208_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3227_);
lean_ctor_set(v_reuseFailAlloc_3234_, 1, v___f_3219_);
v___x_3229_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
size_t v_sz_3230_; size_t v___x_3231_; lean_object* v___x_190__overap_3232_; lean_object* v___x_3233_; 
v_sz_3230_ = lean_array_size(v_a_3183_);
v___x_3231_ = ((size_t)0ULL);
v___x_190__overap_3232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3229_, v___f_3217_, v_sz_3230_, v___x_3231_, v_a_3183_);
lean_inc(v_a_3187_);
lean_inc_ref(v_a_3186_);
lean_inc(v_a_3185_);
lean_inc_ref(v_a_3184_);
v___x_3233_ = lean_apply_5(v___x_190__overap_3232_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, lean_box(0));
return v___x_3233_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___boxed(lean_object* v_00_u03b1_3240_, lean_object* v_inst_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l_Lean_Compiler_LCNF_Probe_toString(v_00_u03b1_3240_, v_inst_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_);
lean_dec(v_a_3246_);
lean_dec_ref(v_a_3245_);
lean_dec(v_a_3244_);
lean_dec_ref(v_a_3243_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___redArg(lean_object* v_data_3249_){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3251_ = lean_array_get_size(v_data_3249_);
v___x_3252_ = lean_unsigned_to_nat(1u);
v___x_3253_ = lean_mk_empty_array_with_capacity(v___x_3252_);
v___x_3254_ = lean_array_push(v___x_3253_, v___x_3251_);
v___x_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___redArg___boxed(lean_object* v_data_3256_, lean_object* v_a_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_Lean_Compiler_LCNF_Probe_count___redArg(v_data_3256_);
lean_dec_ref(v_data_3256_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count(lean_object* v_00_u03b1_3259_, lean_object* v_data_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_){
_start:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3266_ = lean_array_get_size(v_data_3260_);
v___x_3267_ = lean_unsigned_to_nat(1u);
v___x_3268_ = lean_mk_empty_array_with_capacity(v___x_3267_);
v___x_3269_ = lean_array_push(v___x_3268_, v___x_3266_);
v___x_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3269_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___boxed(lean_object* v_00_u03b1_3271_, lean_object* v_data_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Lean_Compiler_LCNF_Probe_count(v_00_u03b1_3271_, v_data_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
lean_dec(v_a_3276_);
lean_dec_ref(v_a_3275_);
lean_dec(v_a_3274_);
lean_dec_ref(v_a_3273_);
lean_dec_ref(v_data_3272_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___redArg(lean_object* v_data_3280_){
_start:
{
lean_object* v___y_3283_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; uint8_t v___x_3291_; 
v___x_3288_ = lean_unsigned_to_nat(0u);
v___x_3289_ = lean_array_get_size(v_data_3280_);
v___x_3290_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v___x_3291_ = lean_nat_dec_lt(v___x_3288_, v___x_3289_);
if (v___x_3291_ == 0)
{
lean_dec_ref(v_data_3280_);
v___y_3283_ = v___x_3288_;
goto v___jp_3282_;
}
else
{
lean_object* v___f_3292_; uint8_t v___x_3293_; 
v___f_3292_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0));
v___x_3293_ = lean_nat_dec_le(v___x_3289_, v___x_3289_);
if (v___x_3293_ == 0)
{
if (v___x_3291_ == 0)
{
lean_dec_ref(v_data_3280_);
v___y_3283_ = v___x_3288_;
goto v___jp_3282_;
}
else
{
size_t v___x_3294_; size_t v___x_3295_; lean_object* v___x_3296_; 
v___x_3294_ = ((size_t)0ULL);
v___x_3295_ = lean_usize_of_nat(v___x_3289_);
v___x_3296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3290_, v___f_3292_, v_data_3280_, v___x_3294_, v___x_3295_, v___x_3288_);
v___y_3283_ = v___x_3296_;
goto v___jp_3282_;
}
}
else
{
size_t v___x_3297_; size_t v___x_3298_; lean_object* v___x_3299_; 
v___x_3297_ = ((size_t)0ULL);
v___x_3298_ = lean_usize_of_nat(v___x_3289_);
v___x_3299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3290_, v___f_3292_, v_data_3280_, v___x_3297_, v___x_3298_, v___x_3288_);
v___y_3283_ = v___x_3299_;
goto v___jp_3282_;
}
}
v___jp_3282_:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3284_ = lean_unsigned_to_nat(1u);
v___x_3285_ = lean_mk_empty_array_with_capacity(v___x_3284_);
v___x_3286_ = lean_array_push(v___x_3285_, v___y_3283_);
v___x_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3286_);
return v___x_3287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___redArg___boxed(lean_object* v_data_3300_, lean_object* v_a_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_Lean_Compiler_LCNF_Probe_sum___redArg(v_data_3300_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum(lean_object* v_data_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_){
_start:
{
lean_object* v___y_3310_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; uint8_t v___x_3318_; 
v___x_3315_ = lean_unsigned_to_nat(0u);
v___x_3316_ = lean_array_get_size(v_data_3303_);
v___x_3317_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v___x_3318_ = lean_nat_dec_lt(v___x_3315_, v___x_3316_);
if (v___x_3318_ == 0)
{
lean_dec_ref(v_data_3303_);
v___y_3310_ = v___x_3315_;
goto v___jp_3309_;
}
else
{
lean_object* v___f_3319_; uint8_t v___x_3320_; 
v___f_3319_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0));
v___x_3320_ = lean_nat_dec_le(v___x_3316_, v___x_3316_);
if (v___x_3320_ == 0)
{
if (v___x_3318_ == 0)
{
lean_dec_ref(v_data_3303_);
v___y_3310_ = v___x_3315_;
goto v___jp_3309_;
}
else
{
size_t v___x_3321_; size_t v___x_3322_; lean_object* v___x_3323_; 
v___x_3321_ = ((size_t)0ULL);
v___x_3322_ = lean_usize_of_nat(v___x_3316_);
v___x_3323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3317_, v___f_3319_, v_data_3303_, v___x_3321_, v___x_3322_, v___x_3315_);
v___y_3310_ = v___x_3323_;
goto v___jp_3309_;
}
}
else
{
size_t v___x_3324_; size_t v___x_3325_; lean_object* v___x_3326_; 
v___x_3324_ = ((size_t)0ULL);
v___x_3325_ = lean_usize_of_nat(v___x_3316_);
v___x_3326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3317_, v___f_3319_, v_data_3303_, v___x_3324_, v___x_3325_, v___x_3315_);
v___y_3310_ = v___x_3326_;
goto v___jp_3309_;
}
}
v___jp_3309_:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3311_ = lean_unsigned_to_nat(1u);
v___x_3312_ = lean_mk_empty_array_with_capacity(v___x_3311_);
v___x_3313_ = lean_array_push(v___x_3312_, v___y_3310_);
v___x_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
return v___x_3314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___boxed(lean_object* v_data_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l_Lean_Compiler_LCNF_Probe_sum(v_data_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_);
lean_dec(v_a_3331_);
lean_dec_ref(v_a_3330_);
lean_dec(v_a_3329_);
lean_dec_ref(v_a_3328_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___redArg(lean_object* v_n_3334_, lean_object* v_data_3335_){
_start:
{
lean_object* v_lower_3338_; lean_object* v_upper_3339_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; uint8_t v___x_3346_; 
v___x_3343_ = lean_array_get_size(v_data_3335_);
v___x_3344_ = lean_nat_sub(v___x_3343_, v_n_3334_);
v___x_3345_ = lean_unsigned_to_nat(0u);
v___x_3346_ = lean_nat_dec_le(v___x_3344_, v___x_3345_);
if (v___x_3346_ == 0)
{
v_lower_3338_ = v___x_3344_;
v_upper_3339_ = v___x_3343_;
goto v___jp_3337_;
}
else
{
lean_dec(v___x_3344_);
v_lower_3338_ = v___x_3345_;
v_upper_3339_ = v___x_3343_;
goto v___jp_3337_;
}
v___jp_3337_:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3340_ = l_Array_toSubarray___redArg(v_data_3335_, v_lower_3338_, v_upper_3339_);
v___x_3341_ = l_Subarray_copy___redArg(v___x_3340_);
v___x_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3341_);
return v___x_3342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___redArg___boxed(lean_object* v_n_3347_, lean_object* v_data_3348_, lean_object* v_a_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Lean_Compiler_LCNF_Probe_tail___redArg(v_n_3347_, v_data_3348_);
lean_dec(v_n_3347_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail(lean_object* v_00_u03b1_3351_, lean_object* v_n_3352_, lean_object* v_data_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_){
_start:
{
lean_object* v_lower_3360_; lean_object* v_upper_3361_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; uint8_t v___x_3368_; 
v___x_3365_ = lean_array_get_size(v_data_3353_);
v___x_3366_ = lean_nat_sub(v___x_3365_, v_n_3352_);
v___x_3367_ = lean_unsigned_to_nat(0u);
v___x_3368_ = lean_nat_dec_le(v___x_3366_, v___x_3367_);
if (v___x_3368_ == 0)
{
v_lower_3360_ = v___x_3366_;
v_upper_3361_ = v___x_3365_;
goto v___jp_3359_;
}
else
{
lean_dec(v___x_3366_);
v_lower_3360_ = v___x_3367_;
v_upper_3361_ = v___x_3365_;
goto v___jp_3359_;
}
v___jp_3359_:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3362_ = l_Array_toSubarray___redArg(v_data_3353_, v_lower_3360_, v_upper_3361_);
v___x_3363_ = l_Subarray_copy___redArg(v___x_3362_);
v___x_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
return v___x_3364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___boxed(lean_object* v_00_u03b1_3369_, lean_object* v_n_3370_, lean_object* v_data_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_Lean_Compiler_LCNF_Probe_tail(v_00_u03b1_3369_, v_n_3370_, v_data_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_);
lean_dec(v_a_3375_);
lean_dec_ref(v_a_3374_);
lean_dec(v_a_3373_);
lean_dec_ref(v_a_3372_);
lean_dec(v_n_3370_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___redArg(lean_object* v_n_3378_, lean_object* v_data_3379_){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3381_ = lean_unsigned_to_nat(0u);
v___x_3382_ = l_Array_toSubarray___redArg(v_data_3379_, v___x_3381_, v_n_3378_);
v___x_3383_ = l_Subarray_copy___redArg(v___x_3382_);
v___x_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3383_);
return v___x_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___redArg___boxed(lean_object* v_n_3385_, lean_object* v_data_3386_, lean_object* v_a_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l_Lean_Compiler_LCNF_Probe_head___redArg(v_n_3385_, v_data_3386_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head(lean_object* v_00_u03b1_3389_, lean_object* v_n_3390_, lean_object* v_data_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3397_ = lean_unsigned_to_nat(0u);
v___x_3398_ = l_Array_toSubarray___redArg(v_data_3391_, v___x_3397_, v_n_3390_);
v___x_3399_ = l_Subarray_copy___redArg(v___x_3398_);
v___x_3400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3399_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___boxed(lean_object* v_00_u03b1_3401_, lean_object* v_n_3402_, lean_object* v_data_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_){
_start:
{
lean_object* v_res_3409_; 
v_res_3409_ = l_Lean_Compiler_LCNF_Probe_head(v_00_u03b1_3401_, v_n_3402_, v_data_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_);
lean_dec(v_a_3407_);
lean_dec_ref(v_a_3406_);
lean_dec(v_a_3405_);
lean_dec_ref(v_a_3404_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0(lean_object* v_probe_3415_, lean_object* v___x_3416_, lean_object* v_inst_3417_, lean_object* v___x_3418_, lean_object* v___x_3419_, lean_object* v_toMonadRef_3420_, lean_object* v___f_3421_, lean_object* v_decls_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v___x_3428_; 
lean_inc(v___y_3426_);
lean_inc_ref(v___y_3425_);
lean_inc(v___y_3424_);
lean_inc_ref(v___y_3423_);
lean_inc_ref(v_decls_3422_);
v___x_3428_ = lean_apply_6(v_probe_3415_, v_decls_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, lean_box(0));
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_toCold_3429_; lean_object* v_options_3430_; uint8_t v_hasTrace_3431_; 
v_toCold_3429_ = lean_ctor_get(v___y_3425_, 0);
v_options_3430_ = lean_ctor_get(v_toCold_3429_, 2);
v_hasTrace_3431_ = lean_ctor_get_uint8(v_options_3430_, sizeof(void*)*1);
if (v_hasTrace_3431_ == 0)
{
lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
lean_dec_ref(v___f_3421_);
lean_dec_ref(v_toMonadRef_3420_);
lean_dec_ref(v___x_3419_);
lean_dec_ref(v___x_3418_);
lean_dec_ref(v_inst_3417_);
lean_dec_ref(v___x_3416_);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3438_ == 0)
{
lean_object* v_unused_3439_; 
v_unused_3439_ = lean_ctor_get(v___x_3428_, 0);
lean_dec(v_unused_3439_);
v___x_3433_ = v___x_3428_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_dec(v___x_3428_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 0, v_decls_3422_);
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_decls_3422_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
else
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3477_; 
v_a_3440_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3442_ = v___x_3428_;
v_isShared_3443_ = v_isSharedCheck_3477_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3428_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3477_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v_inheritedTraceOptions_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; uint8_t v___x_3449_; 
v_inheritedTraceOptions_3444_ = lean_ctor_get(v_toCold_3429_, 11);
v___x_3445_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0));
v___x_3446_ = l_Lean_Name_mkStr2(v___x_3445_, v___x_3416_);
v___x_3447_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__2));
lean_inc(v___x_3446_);
v___x_3448_ = l_Lean_Name_append(v___x_3447_, v___x_3446_);
v___x_3449_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3444_, v_options_3430_, v___x_3448_);
lean_dec(v___x_3448_);
if (v___x_3449_ == 0)
{
lean_object* v___x_3451_; 
lean_dec(v___x_3446_);
lean_dec(v_a_3440_);
lean_dec_ref(v___f_3421_);
lean_dec_ref(v_toMonadRef_3420_);
lean_dec_ref(v___x_3419_);
lean_dec_ref(v___x_3418_);
lean_dec_ref(v_inst_3417_);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 0, v_decls_3422_);
v___x_3451_ = v___x_3442_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_decls_3422_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
else
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_961__overap_3459_; lean_object* v___x_3460_; 
lean_del_object(v___x_3442_);
v___x_3453_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__3));
v___x_3454_ = lean_array_to_list(v_a_3440_);
v___x_3455_ = l_List_toString___redArg(v_inst_3417_, v___x_3454_);
v___x_3456_ = lean_string_append(v___x_3453_, v___x_3455_);
lean_dec_ref(v___x_3455_);
v___x_3457_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
v___x_3458_ = l_Lean_MessageData_ofFormat(v___x_3457_);
v___x_961__overap_3459_ = l_Lean_addTrace___redArg(v___x_3418_, v___x_3419_, v_toMonadRef_3420_, v___f_3421_, v___x_3446_, v___x_3458_);
lean_inc(v___y_3426_);
lean_inc_ref(v___y_3425_);
lean_inc(v___y_3424_);
lean_inc_ref(v___y_3423_);
v___x_3460_ = lean_apply_5(v___x_961__overap_3459_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, lean_box(0));
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3467_ == 0)
{
lean_object* v_unused_3468_; 
v_unused_3468_ = lean_ctor_get(v___x_3460_, 0);
lean_dec(v_unused_3468_);
v___x_3462_ = v___x_3460_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_dec(v___x_3460_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
lean_ctor_set(v___x_3462_, 0, v_decls_3422_);
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_decls_3422_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_dec_ref(v_decls_3422_);
v_a_3469_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3460_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3460_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3485_; 
lean_dec_ref(v_decls_3422_);
lean_dec_ref(v___f_3421_);
lean_dec_ref(v_toMonadRef_3420_);
lean_dec_ref(v___x_3419_);
lean_dec_ref(v___x_3418_);
lean_dec_ref(v_inst_3417_);
lean_dec_ref(v___x_3416_);
v_a_3478_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3480_ = v___x_3428_;
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3428_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
if (v_isShared_3481_ == 0)
{
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___boxed(lean_object* v_probe_3486_, lean_object* v___x_3487_, lean_object* v_inst_3488_, lean_object* v___x_3489_, lean_object* v___x_3490_, lean_object* v_toMonadRef_3491_, lean_object* v___f_3492_, lean_object* v_decls_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_){
_start:
{
lean_object* v_res_3499_; 
v_res_3499_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0(v_probe_3486_, v___x_3487_, v_inst_3488_, v___x_3489_, v___x_3490_, v_toMonadRef_3491_, v___f_3492_, v_decls_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
return v_res_3499_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2(void){
_start:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3502_ = l_Lean_Core_instMonadTraceCoreM;
v___x_3503_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1));
v___x_3504_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_3503_, v___x_3502_);
return v___x_3504_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3(void){
_start:
{
lean_object* v___x_3505_; lean_object* v___f_3506_; lean_object* v___x_3507_; 
v___x_3505_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2);
v___f_3506_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0));
v___x_3507_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3506_, v___x_3505_);
return v___x_3507_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6(void){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3510_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_3511_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1));
v___x_3512_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__5));
v___x_3513_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_3512_, v___x_3511_, v___x_3510_);
return v___x_3513_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7(void){
_start:
{
lean_object* v___x_3514_; lean_object* v___f_3515_; lean_object* v___f_3516_; lean_object* v___x_3517_; 
v___x_3514_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6);
v___f_3515_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0));
v___f_3516_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4));
v___x_3517_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_3516_, v___f_3515_, v___x_3514_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg(lean_object* v_inst_3522_, uint8_t v_phase_3523_, lean_object* v_probe_3524_){
_start:
{
lean_object* v___x_3525_; lean_object* v_toApplicative_3526_; lean_object* v_toFunctor_3527_; lean_object* v_toSeq_3528_; lean_object* v_toSeqLeft_3529_; lean_object* v_toSeqRight_3530_; lean_object* v___f_3531_; lean_object* v___f_3532_; lean_object* v___f_3533_; lean_object* v___f_3534_; lean_object* v___x_3535_; lean_object* v___f_3536_; lean_object* v___f_3537_; lean_object* v___f_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v_toApplicative_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3579_; 
v___x_3525_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3526_ = lean_ctor_get(v___x_3525_, 0);
v_toFunctor_3527_ = lean_ctor_get(v_toApplicative_3526_, 0);
v_toSeq_3528_ = lean_ctor_get(v_toApplicative_3526_, 2);
v_toSeqLeft_3529_ = lean_ctor_get(v_toApplicative_3526_, 3);
v_toSeqRight_3530_ = lean_ctor_get(v_toApplicative_3526_, 4);
v___f_3531_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3532_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3527_, 2);
v___f_3533_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3533_, 0, v_toFunctor_3527_);
v___f_3534_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3534_, 0, v_toFunctor_3527_);
v___x_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___f_3533_);
lean_ctor_set(v___x_3535_, 1, v___f_3534_);
lean_inc(v_toSeqRight_3530_);
v___f_3536_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3536_, 0, v_toSeqRight_3530_);
lean_inc(v_toSeqLeft_3529_);
v___f_3537_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3537_, 0, v_toSeqLeft_3529_);
lean_inc(v_toSeq_3528_);
v___f_3538_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3538_, 0, v_toSeq_3528_);
v___x_3539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3535_);
lean_ctor_set(v___x_3539_, 1, v___f_3531_);
lean_ctor_set(v___x_3539_, 2, v___f_3538_);
lean_ctor_set(v___x_3539_, 3, v___f_3537_);
lean_ctor_set(v___x_3539_, 4, v___f_3536_);
v___x_3540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3539_);
lean_ctor_set(v___x_3540_, 1, v___f_3532_);
v___x_3541_ = l_StateRefT_x27_instMonad___redArg(v___x_3540_);
v_toApplicative_3542_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3579_ == 0)
{
lean_object* v_unused_3580_; 
v_unused_3580_ = lean_ctor_get(v___x_3541_, 1);
lean_dec(v_unused_3580_);
v___x_3544_ = v___x_3541_;
v_isShared_3545_ = v_isSharedCheck_3579_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_toApplicative_3542_);
lean_dec(v___x_3541_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3579_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v_toFunctor_3546_; lean_object* v_toSeq_3547_; lean_object* v_toSeqLeft_3548_; lean_object* v_toSeqRight_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3577_; 
v_toFunctor_3546_ = lean_ctor_get(v_toApplicative_3542_, 0);
v_toSeq_3547_ = lean_ctor_get(v_toApplicative_3542_, 2);
v_toSeqLeft_3548_ = lean_ctor_get(v_toApplicative_3542_, 3);
v_toSeqRight_3549_ = lean_ctor_get(v_toApplicative_3542_, 4);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_toApplicative_3542_);
if (v_isSharedCheck_3577_ == 0)
{
lean_object* v_unused_3578_; 
v_unused_3578_ = lean_ctor_get(v_toApplicative_3542_, 1);
lean_dec(v_unused_3578_);
v___x_3551_ = v_toApplicative_3542_;
v_isShared_3552_ = v_isSharedCheck_3577_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_toSeqRight_3549_);
lean_inc(v_toSeqLeft_3548_);
lean_inc(v_toSeq_3547_);
lean_inc(v_toFunctor_3546_);
lean_dec(v_toApplicative_3542_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3577_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___f_3553_; lean_object* v___f_3554_; lean_object* v___f_3555_; lean_object* v___f_3556_; lean_object* v___x_3557_; lean_object* v___f_3558_; lean_object* v___f_3559_; lean_object* v___f_3560_; lean_object* v___x_3562_; 
v___f_3553_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3554_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3546_);
v___f_3555_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3555_, 0, v_toFunctor_3546_);
v___f_3556_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3556_, 0, v_toFunctor_3546_);
v___x_3557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___f_3555_);
lean_ctor_set(v___x_3557_, 1, v___f_3556_);
v___f_3558_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3558_, 0, v_toSeqRight_3549_);
v___f_3559_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3559_, 0, v_toSeqLeft_3548_);
v___f_3560_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3560_, 0, v_toSeq_3547_);
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 4, v___f_3558_);
lean_ctor_set(v___x_3551_, 3, v___f_3559_);
lean_ctor_set(v___x_3551_, 2, v___f_3560_);
lean_ctor_set(v___x_3551_, 1, v___f_3553_);
lean_ctor_set(v___x_3551_, 0, v___x_3557_);
v___x_3562_ = v___x_3551_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3557_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v___f_3553_);
lean_ctor_set(v_reuseFailAlloc_3576_, 2, v___f_3560_);
lean_ctor_set(v_reuseFailAlloc_3576_, 3, v___f_3559_);
lean_ctor_set(v_reuseFailAlloc_3576_, 4, v___f_3558_);
v___x_3562_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
lean_object* v___x_3564_; 
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 1, v___f_3554_);
lean_ctor_set(v___x_3544_, 0, v___x_3562_);
v___x_3564_ = v___x_3544_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3562_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v___f_3554_);
v___x_3564_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v_toMonadRef_3567_; lean_object* v___f_3568_; lean_object* v___x_3569_; uint8_t v___x_3570_; lean_object* v___x_3571_; lean_object* v___f_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3565_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3);
v___x_3566_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7);
v_toMonadRef_3567_ = lean_ctor_get(v___x_3566_, 0);
v___f_3568_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__8));
v___x_3569_ = lean_unsigned_to_nat(0u);
v___x_3570_ = 0;
v___x_3571_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__9));
lean_inc_ref(v_toMonadRef_3567_);
v___f_3572_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_3572_, 0, v_probe_3524_);
lean_closure_set(v___f_3572_, 1, v___x_3571_);
lean_closure_set(v___f_3572_, 2, v_inst_3522_);
lean_closure_set(v___f_3572_, 3, v___x_3564_);
lean_closure_set(v___f_3572_, 4, v___x_3565_);
lean_closure_set(v___f_3572_, 5, v_toMonadRef_3567_);
lean_closure_set(v___f_3572_, 6, v___f_3568_);
v___x_3573_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__10));
v___x_3574_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3574_, 0, v___x_3569_);
lean_ctor_set(v___x_3574_, 1, v___x_3573_);
lean_ctor_set(v___x_3574_, 2, v___f_3572_);
lean_ctor_set_uint8(v___x_3574_, sizeof(void*)*3, v_phase_3523_);
lean_ctor_set_uint8(v___x_3574_, sizeof(void*)*3 + 1, v_phase_3523_);
lean_ctor_set_uint8(v___x_3574_, sizeof(void*)*3 + 2, v___x_3570_);
return v___x_3574_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___boxed(lean_object* v_inst_3581_, lean_object* v_phase_3582_, lean_object* v_probe_3583_){
_start:
{
uint8_t v_phase_boxed_3584_; lean_object* v_res_3585_; 
v_phase_boxed_3584_ = lean_unbox(v_phase_3582_);
v_res_3585_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg(v_inst_3581_, v_phase_boxed_3584_, v_probe_3583_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass(lean_object* v_00_u03b2_3586_, lean_object* v_inst_3587_, uint8_t v_phase_3588_, lean_object* v_probe_3589_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg(v_inst_3587_, v_phase_3588_, v_probe_3589_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___boxed(lean_object* v_00_u03b2_3591_, lean_object* v_inst_3592_, lean_object* v_phase_3593_, lean_object* v_probe_3594_){
_start:
{
uint8_t v_phase_boxed_3595_; lean_object* v_res_3596_; 
v_phase_boxed_3595_ = lean_unbox(v_phase_3593_);
v_res_3596_ = l_Lean_Compiler_LCNF_Probe_toPass(v_00_u03b2_3591_, v_inst_3592_, v_phase_boxed_3595_, v_probe_3594_);
return v_res_3596_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3655_ = lean_unsigned_to_nat(4008565020u);
v___x_3656_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3657_ = l_Lean_Name_num___override(v___x_3656_, v___x_3655_);
return v___x_3657_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3659_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3660_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3661_ = l_Lean_Name_str___override(v___x_3660_, v___x_3659_);
return v___x_3661_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3663_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3664_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3665_ = l_Lean_Name_str___override(v___x_3664_, v___x_3663_);
return v___x_3665_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3666_ = lean_unsigned_to_nat(2u);
v___x_3667_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3668_ = l_Lean_Name_num___override(v___x_3667_, v___x_3666_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3670_; uint8_t v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3670_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3671_ = 1;
v___x_3672_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3673_ = l_Lean_registerTraceClass(v___x_3670_, v___x_3671_, v___x_3672_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2____boxed(lean_object* v_a_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_();
return v_res_3675_;
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
