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
lean_object* v___x_190_; lean_object* v_toApplicative_191_; lean_object* v_toFunctor_192_; lean_object* v_toSeq_193_; lean_object* v_toSeqLeft_194_; lean_object* v_toSeqRight_195_; lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___x_200_; lean_object* v___f_201_; lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v_toApplicative_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_244_; 
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
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; 
v_unused_245_ = lean_ctor_get(v___x_206_, 1);
lean_dec(v_unused_245_);
v___x_209_ = v___x_206_;
v_isShared_210_ = v_isSharedCheck_244_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_toApplicative_207_);
lean_dec(v___x_206_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_244_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v_toFunctor_211_; lean_object* v_toSeq_212_; lean_object* v_toSeqLeft_213_; lean_object* v_toSeqRight_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_242_; 
v_toFunctor_211_ = lean_ctor_get(v_toApplicative_207_, 0);
v_toSeq_212_ = lean_ctor_get(v_toApplicative_207_, 2);
v_toSeqLeft_213_ = lean_ctor_get(v_toApplicative_207_, 3);
v_toSeqRight_214_ = lean_ctor_get(v_toApplicative_207_, 4);
v_isSharedCheck_242_ = !lean_is_exclusive(v_toApplicative_207_);
if (v_isSharedCheck_242_ == 0)
{
lean_object* v_unused_243_; 
v_unused_243_ = lean_ctor_get(v_toApplicative_207_, 1);
lean_dec(v_unused_243_);
v___x_216_ = v_toApplicative_207_;
v_isShared_217_ = v_isSharedCheck_242_;
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
v_isShared_217_ = v_isSharedCheck_242_;
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
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v___f_218_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v___f_225_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v___f_224_);
lean_ctor_set(v_reuseFailAlloc_241_, 4, v___f_223_);
v___x_227_ = v_reuseFailAlloc_241_;
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
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v___f_219_);
v___x_229_ = v_reuseFailAlloc_240_;
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
lean_object* v___f_235_; size_t v___x_236_; size_t v___x_237_; lean_object* v___x_348__overap_238_; lean_object* v___x_239_; 
v___f_235_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_235_, 0, v_f_183_);
v___x_236_ = ((size_t)0ULL);
v___x_237_ = lean_usize_of_nat(v___x_231_);
v___x_348__overap_238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_229_, v___f_235_, v_data_184_, v___x_236_, v___x_237_, v___x_232_);
lean_inc(v_a_188_);
lean_inc_ref(v_a_187_);
lean_inc(v_a_186_);
lean_inc_ref(v_a_185_);
v___x_239_ = lean_apply_5(v___x_348__overap_238_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, lean_box(0));
return v___x_239_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter___redArg___boxed(lean_object* v_f_246_, lean_object* v_data_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Compiler_LCNF_Probe_filter___redArg(v_f_246_, v_data_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter(lean_object* v_00_u03b1_254_, lean_object* v_f_255_, lean_object* v_data_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v___x_262_; lean_object* v_toApplicative_263_; lean_object* v_toFunctor_264_; lean_object* v_toSeq_265_; lean_object* v_toSeqLeft_266_; lean_object* v_toSeqRight_267_; lean_object* v___f_268_; lean_object* v___f_269_; lean_object* v___f_270_; lean_object* v___f_271_; lean_object* v___x_272_; lean_object* v___f_273_; lean_object* v___f_274_; lean_object* v___f_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_toApplicative_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_316_; 
v___x_262_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_263_ = lean_ctor_get(v___x_262_, 0);
v_toFunctor_264_ = lean_ctor_get(v_toApplicative_263_, 0);
v_toSeq_265_ = lean_ctor_get(v_toApplicative_263_, 2);
v_toSeqLeft_266_ = lean_ctor_get(v_toApplicative_263_, 3);
v_toSeqRight_267_ = lean_ctor_get(v_toApplicative_263_, 4);
v___f_268_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_269_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_264_, 2);
v___f_270_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_270_, 0, v_toFunctor_264_);
v___f_271_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_271_, 0, v_toFunctor_264_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___f_270_);
lean_ctor_set(v___x_272_, 1, v___f_271_);
lean_inc(v_toSeqRight_267_);
v___f_273_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_273_, 0, v_toSeqRight_267_);
lean_inc(v_toSeqLeft_266_);
v___f_274_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_274_, 0, v_toSeqLeft_266_);
lean_inc(v_toSeq_265_);
v___f_275_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_275_, 0, v_toSeq_265_);
v___x_276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_276_, 0, v___x_272_);
lean_ctor_set(v___x_276_, 1, v___f_268_);
lean_ctor_set(v___x_276_, 2, v___f_275_);
lean_ctor_set(v___x_276_, 3, v___f_274_);
lean_ctor_set(v___x_276_, 4, v___f_273_);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v___f_269_);
v___x_278_ = l_StateRefT_x27_instMonad___redArg(v___x_277_);
v_toApplicative_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_316_ == 0)
{
lean_object* v_unused_317_; 
v_unused_317_ = lean_ctor_get(v___x_278_, 1);
lean_dec(v_unused_317_);
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_316_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_toApplicative_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_316_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v_toFunctor_283_; lean_object* v_toSeq_284_; lean_object* v_toSeqLeft_285_; lean_object* v_toSeqRight_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_314_; 
v_toFunctor_283_ = lean_ctor_get(v_toApplicative_279_, 0);
v_toSeq_284_ = lean_ctor_get(v_toApplicative_279_, 2);
v_toSeqLeft_285_ = lean_ctor_get(v_toApplicative_279_, 3);
v_toSeqRight_286_ = lean_ctor_get(v_toApplicative_279_, 4);
v_isSharedCheck_314_ = !lean_is_exclusive(v_toApplicative_279_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; 
v_unused_315_ = lean_ctor_get(v_toApplicative_279_, 1);
lean_dec(v_unused_315_);
v___x_288_ = v_toApplicative_279_;
v_isShared_289_ = v_isSharedCheck_314_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_toSeqRight_286_);
lean_inc(v_toSeqLeft_285_);
lean_inc(v_toSeq_284_);
lean_inc(v_toFunctor_283_);
lean_dec(v_toApplicative_279_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_314_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___f_290_; lean_object* v___f_291_; lean_object* v___f_292_; lean_object* v___f_293_; lean_object* v___x_294_; lean_object* v___f_295_; lean_object* v___f_296_; lean_object* v___f_297_; lean_object* v___x_299_; 
v___f_290_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_291_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_283_);
v___f_292_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_292_, 0, v_toFunctor_283_);
v___f_293_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_293_, 0, v_toFunctor_283_);
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v___f_292_);
lean_ctor_set(v___x_294_, 1, v___f_293_);
v___f_295_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_295_, 0, v_toSeqRight_286_);
v___f_296_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_296_, 0, v_toSeqLeft_285_);
v___f_297_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_297_, 0, v_toSeq_284_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 4, v___f_295_);
lean_ctor_set(v___x_288_, 3, v___f_296_);
lean_ctor_set(v___x_288_, 2, v___f_297_);
lean_ctor_set(v___x_288_, 1, v___f_290_);
lean_ctor_set(v___x_288_, 0, v___x_294_);
v___x_299_ = v___x_288_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_294_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v___f_290_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v___f_297_);
lean_ctor_set(v_reuseFailAlloc_313_, 3, v___f_296_);
lean_ctor_set(v_reuseFailAlloc_313_, 4, v___f_295_);
v___x_299_ = v_reuseFailAlloc_313_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_301_; 
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 1, v___f_291_);
lean_ctor_set(v___x_281_, 0, v___x_299_);
v___x_301_ = v___x_281_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v___f_291_);
v___x_301_ = v_reuseFailAlloc_312_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_array_get_size(v_data_256_);
v___x_304_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filter___redArg___closed__0));
v___x_305_ = lean_nat_dec_lt(v___x_302_, v___x_303_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; 
lean_dec_ref(v___x_301_);
lean_dec_ref(v_data_256_);
lean_dec_ref(v_f_255_);
v___x_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_304_);
return v___x_306_;
}
else
{
lean_object* v___f_307_; size_t v___x_308_; size_t v___x_309_; lean_object* v___x_434__overap_310_; lean_object* v___x_311_; 
v___f_307_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_307_, 0, v_f_255_);
v___x_308_ = ((size_t)0ULL);
v___x_309_ = lean_usize_of_nat(v___x_303_);
v___x_434__overap_310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_301_, v___f_307_, v_data_256_, v___x_308_, v___x_309_, v___x_304_);
lean_inc(v_a_260_);
lean_inc_ref(v_a_259_);
lean_inc(v_a_258_);
lean_inc_ref(v_a_257_);
v___x_311_ = lean_apply_5(v___x_434__overap_310_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, lean_box(0));
return v___x_311_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter___boxed(lean_object* v_00_u03b1_318_, lean_object* v_f_319_, lean_object* v_data_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_Compiler_LCNF_Probe_filter(v_00_u03b1_318_, v_f_319_, v_data_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
return v_res_326_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0(lean_object* v_inst_327_, lean_object* v_x1_328_, lean_object* v_x2_329_){
_start:
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = lean_apply_2(v_inst_327_, v_x1_328_, v_x2_329_);
v___x_331_ = lean_unbox(v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0___boxed(lean_object* v_inst_332_, lean_object* v_x1_333_, lean_object* v_x2_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0(v_inst_332_, v_x1_333_, v_x2_334_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted___redArg(lean_object* v_inst_337_, lean_object* v_data_338_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_340_ = lean_array_get_size(v_data_338_);
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_nat_dec_eq(v___x_340_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___f_343_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___y_352_; uint8_t v___x_354_; 
v___f_343_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_343_, 0, v_inst_337_);
v___x_349_ = lean_unsigned_to_nat(1u);
v___x_350_ = lean_nat_sub(v___x_340_, v___x_349_);
v___x_354_ = lean_nat_dec_le(v___x_341_, v___x_350_);
if (v___x_354_ == 0)
{
lean_inc(v___x_350_);
v___y_352_ = v___x_350_;
goto v___jp_351_;
}
else
{
v___y_352_ = v___x_341_;
goto v___jp_351_;
}
v___jp_344_:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_343_, v___x_340_, v_data_338_, v___y_345_, v___y_346_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_346_);
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
v___jp_351_:
{
uint8_t v___x_353_; 
v___x_353_ = lean_nat_dec_le(v___y_352_, v___x_350_);
if (v___x_353_ == 0)
{
lean_dec(v___x_350_);
lean_inc(v___y_352_);
v___y_345_ = v___y_352_;
v___y_346_ = v___y_352_;
goto v___jp_344_;
}
else
{
v___y_345_ = v___y_352_;
v___y_346_ = v___x_350_;
goto v___jp_344_;
}
}
}
else
{
lean_object* v___x_355_; 
lean_dec_ref(v_inst_337_);
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v_data_338_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted___redArg___boxed(lean_object* v_inst_356_, lean_object* v_data_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Compiler_LCNF_Probe_sorted___redArg(v_inst_356_, v_data_357_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted(lean_object* v_00_u03b1_360_, lean_object* v_inst_361_, lean_object* v_inst_362_, lean_object* v_inst_363_, lean_object* v_data_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_370_ = lean_array_get_size(v_data_364_);
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = lean_nat_dec_eq(v___x_370_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___f_373_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___y_382_; uint8_t v___x_384_; 
v___f_373_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_373_, 0, v_inst_363_);
v___x_379_ = lean_unsigned_to_nat(1u);
v___x_380_ = lean_nat_sub(v___x_370_, v___x_379_);
v___x_384_ = lean_nat_dec_le(v___x_371_, v___x_380_);
if (v___x_384_ == 0)
{
lean_inc(v___x_380_);
v___y_382_ = v___x_380_;
goto v___jp_381_;
}
else
{
v___y_382_ = v___x_371_;
goto v___jp_381_;
}
v___jp_374_:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_373_, v___x_370_, v_data_364_, v___y_375_, v___y_376_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_376_);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
v___jp_381_:
{
uint8_t v___x_383_; 
v___x_383_ = lean_nat_dec_le(v___y_382_, v___x_380_);
if (v___x_383_ == 0)
{
lean_dec(v___x_380_);
lean_inc(v___y_382_);
v___y_375_ = v___y_382_;
v___y_376_ = v___y_382_;
goto v___jp_374_;
}
else
{
v___y_375_ = v___y_382_;
v___y_376_ = v___x_380_;
goto v___jp_374_;
}
}
}
else
{
lean_object* v___x_385_; 
lean_dec_ref(v_inst_363_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v_data_364_);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted___boxed(lean_object* v_00_u03b1_386_, lean_object* v_inst_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_data_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Compiler_LCNF_Probe_sorted(v_00_u03b1_386_, v_inst_387_, v_inst_388_, v_inst_389_, v_data_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_inst_387_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0(uint8_t v_pu_397_, lean_object* v_x_398_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = l_Lean_Compiler_LCNF_Decl_size(v_pu_397_, v_x_398_);
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set(v___x_400_, 1, v_x_398_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0___boxed(lean_object* v_pu_401_, lean_object* v_x_402_){
_start:
{
uint8_t v_pu_boxed_403_; lean_object* v_res_404_; 
v_pu_boxed_403_ = lean_unbox(v_pu_401_);
v_res_404_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0(v_pu_boxed_403_, v_x_402_);
return v_res_404_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1(lean_object* v_x_405_, lean_object* v_x_406_){
_start:
{
lean_object* v_fst_407_; lean_object* v_snd_408_; lean_object* v_fst_409_; lean_object* v_snd_410_; uint8_t v___x_411_; 
v_fst_407_ = lean_ctor_get(v_x_405_, 0);
v_snd_408_ = lean_ctor_get(v_x_405_, 1);
v_fst_409_ = lean_ctor_get(v_x_406_, 0);
v_snd_410_ = lean_ctor_get(v_x_406_, 1);
v___x_411_ = lean_nat_dec_eq(v_fst_407_, v_fst_409_);
if (v___x_411_ == 0)
{
uint8_t v___x_412_; 
v___x_412_ = lean_nat_dec_lt(v_fst_407_, v_fst_409_);
return v___x_412_;
}
else
{
lean_object* v_toSignature_413_; lean_object* v_toSignature_414_; lean_object* v_name_415_; lean_object* v_name_416_; uint8_t v___x_417_; 
v_toSignature_413_ = lean_ctor_get(v_snd_408_, 0);
v_toSignature_414_ = lean_ctor_get(v_snd_410_, 0);
v_name_415_ = lean_ctor_get(v_toSignature_413_, 0);
v_name_416_ = lean_ctor_get(v_toSignature_414_, 0);
v___x_417_ = l_Lean_Name_lt(v_name_415_, v_name_416_);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1___boxed(lean_object* v_x_418_, lean_object* v_x_419_){
_start:
{
uint8_t v_res_420_; lean_object* v_r_421_; 
v_res_420_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1(v_x_418_, v_x_419_);
lean_dec_ref(v_x_419_);
lean_dec_ref(v_x_418_);
v_r_421_ = lean_box(v_res_420_);
return v_r_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg(uint8_t v_pu_442_, lean_object* v_decls_443_){
_start:
{
lean_object* v___x_445_; lean_object* v___f_446_; lean_object* v___x_447_; size_t v_sz_448_; size_t v___x_449_; lean_object* v_decls_450_; lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_445_ = lean_box(v_pu_442_);
v___f_446_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_446_, 0, v___x_445_);
v___x_447_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v_sz_448_ = lean_array_size(v_decls_443_);
v___x_449_ = ((size_t)0ULL);
v_decls_450_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_447_, v___f_446_, v_sz_448_, v___x_449_, v_decls_443_);
v___x_451_ = lean_array_get_size(v_decls_450_);
v___x_452_ = lean_unsigned_to_nat(0u);
v___x_453_ = lean_nat_dec_eq(v___x_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___f_454_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___y_463_; uint8_t v___x_465_; 
v___f_454_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__10));
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = lean_nat_sub(v___x_451_, v___x_460_);
v___x_465_ = lean_nat_dec_le(v___x_452_, v___x_461_);
if (v___x_465_ == 0)
{
lean_inc(v___x_461_);
v___y_463_ = v___x_461_;
goto v___jp_462_;
}
else
{
v___y_463_ = v___x_452_;
goto v___jp_462_;
}
v___jp_455_:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_454_, v___x_451_, v_decls_450_, v___y_456_, v___y_457_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_457_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
return v___x_459_;
}
v___jp_462_:
{
uint8_t v___x_464_; 
v___x_464_ = lean_nat_dec_le(v___y_463_, v___x_461_);
if (v___x_464_ == 0)
{
lean_dec(v___x_461_);
lean_inc(v___y_463_);
v___y_456_ = v___y_463_;
v___y_457_ = v___y_463_;
goto v___jp_455_;
}
else
{
v___y_456_ = v___y_463_;
v___y_457_ = v___x_461_;
goto v___jp_455_;
}
}
}
else
{
lean_object* v___x_466_; 
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v_decls_450_);
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___boxed(lean_object* v_pu_467_, lean_object* v_decls_468_, lean_object* v_a_469_){
_start:
{
uint8_t v_pu_boxed_470_; lean_object* v_res_471_; 
v_pu_boxed_470_ = lean_unbox(v_pu_467_);
v_res_471_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg(v_pu_boxed_470_, v_decls_468_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize(uint8_t v_pu_472_, lean_object* v_decls_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_479_; lean_object* v___f_480_; lean_object* v___x_481_; size_t v_sz_482_; size_t v___x_483_; lean_object* v_decls_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_479_ = lean_box(v_pu_472_);
v___f_480_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_480_, 0, v___x_479_);
v___x_481_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v_sz_482_ = lean_array_size(v_decls_473_);
v___x_483_ = ((size_t)0ULL);
v_decls_484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_481_, v___f_480_, v_sz_482_, v___x_483_, v_decls_473_);
v___x_485_ = lean_array_get_size(v_decls_484_);
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = lean_nat_dec_eq(v___x_485_, v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___f_488_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___y_497_; uint8_t v___x_499_; 
v___f_488_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__10));
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = lean_nat_sub(v___x_485_, v___x_494_);
v___x_499_ = lean_nat_dec_le(v___x_486_, v___x_495_);
if (v___x_499_ == 0)
{
lean_inc(v___x_495_);
v___y_497_ = v___x_495_;
goto v___jp_496_;
}
else
{
v___y_497_ = v___x_486_;
goto v___jp_496_;
}
v___jp_489_:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_488_, v___x_485_, v_decls_484_, v___y_490_, v___y_491_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_491_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
v___jp_496_:
{
uint8_t v___x_498_; 
v___x_498_ = lean_nat_dec_le(v___y_497_, v___x_495_);
if (v___x_498_ == 0)
{
lean_dec(v___x_495_);
lean_inc(v___y_497_);
v___y_490_ = v___y_497_;
v___y_491_ = v___y_497_;
goto v___jp_489_;
}
else
{
v___y_490_ = v___y_497_;
v___y_491_ = v___x_495_;
goto v___jp_489_;
}
}
}
else
{
lean_object* v___x_500_; 
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v_decls_484_);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___boxed(lean_object* v_pu_501_, lean_object* v_decls_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
uint8_t v_pu_boxed_508_; lean_object* v_res_509_; 
v_pu_boxed_508_ = lean_unbox(v_pu_501_);
v_res_509_ = l_Lean_Compiler_LCNF_Probe_sortedBySize(v_pu_boxed_508_, v_decls_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0(lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_a_512_, lean_object* v_x_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v___x_520_; 
lean_inc(v_a_512_);
lean_inc_ref(v_inst_511_);
lean_inc_ref(v_inst_510_);
v___x_520_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_510_, v_inst_511_, v___y_514_, v_a_512_);
if (lean_obj_tag(v___x_520_) == 1)
{
lean_object* v_val_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_532_; 
v_val_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_532_ == 0)
{
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_532_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_val_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_532_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = lean_nat_add(v_val_521_, v___x_525_);
lean_dec(v_val_521_);
v___x_527_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_510_, v_inst_511_, v___y_514_, v_a_512_, v___x_526_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_527_);
v___x_529_ = v___x_523_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_531_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_530_; 
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v___x_520_);
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_510_, v_inst_511_, v___y_514_, v_a_512_, v___x_533_);
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0___boxed(lean_object* v_inst_537_, lean_object* v_inst_538_, lean_object* v_a_539_, lean_object* v_x_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0(v_inst_537_, v_inst_538_, v_a_539_, v_x_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__1(lean_object* v_x1_548_, lean_object* v_x2_549_, lean_object* v_x3_550_){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v_x2_549_);
lean_ctor_set(v___x_551_, 1, v_x3_550_);
v___x_552_ = lean_array_push(v_x1_548_, v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__2(lean_object* v___x_553_, lean_object* v___f_554_, lean_object* v_acc_555_, lean_object* v_l_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_553_, v___f_554_, v_acc_555_, v_l_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg(lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_data_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v___x_570_; lean_object* v_toApplicative_571_; lean_object* v_toFunctor_572_; lean_object* v_toSeq_573_; lean_object* v_toSeqLeft_574_; lean_object* v_toSeqRight_575_; lean_object* v___f_576_; lean_object* v___f_577_; lean_object* v___f_578_; lean_object* v___f_579_; lean_object* v___x_580_; lean_object* v___f_581_; lean_object* v___f_582_; lean_object* v___f_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v_toApplicative_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_657_; 
v___x_570_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_571_ = lean_ctor_get(v___x_570_, 0);
v_toFunctor_572_ = lean_ctor_get(v_toApplicative_571_, 0);
v_toSeq_573_ = lean_ctor_get(v_toApplicative_571_, 2);
v_toSeqLeft_574_ = lean_ctor_get(v_toApplicative_571_, 3);
v_toSeqRight_575_ = lean_ctor_get(v_toApplicative_571_, 4);
v___f_576_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_577_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_572_, 2);
v___f_578_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_578_, 0, v_toFunctor_572_);
v___f_579_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_579_, 0, v_toFunctor_572_);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v___f_578_);
lean_ctor_set(v___x_580_, 1, v___f_579_);
lean_inc(v_toSeqRight_575_);
v___f_581_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_581_, 0, v_toSeqRight_575_);
lean_inc(v_toSeqLeft_574_);
v___f_582_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_582_, 0, v_toSeqLeft_574_);
lean_inc(v_toSeq_573_);
v___f_583_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_583_, 0, v_toSeq_573_);
v___x_584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_584_, 0, v___x_580_);
lean_ctor_set(v___x_584_, 1, v___f_576_);
lean_ctor_set(v___x_584_, 2, v___f_583_);
lean_ctor_set(v___x_584_, 3, v___f_582_);
lean_ctor_set(v___x_584_, 4, v___f_581_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v___f_577_);
v___x_586_ = l_StateRefT_x27_instMonad___redArg(v___x_585_);
v_toApplicative_587_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; 
v_unused_658_ = lean_ctor_get(v___x_586_, 1);
lean_dec(v_unused_658_);
v___x_589_ = v___x_586_;
v_isShared_590_ = v_isSharedCheck_657_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_toApplicative_587_);
lean_dec(v___x_586_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_657_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v_toFunctor_591_; lean_object* v_toSeq_592_; lean_object* v_toSeqLeft_593_; lean_object* v_toSeqRight_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_655_; 
v_toFunctor_591_ = lean_ctor_get(v_toApplicative_587_, 0);
v_toSeq_592_ = lean_ctor_get(v_toApplicative_587_, 2);
v_toSeqLeft_593_ = lean_ctor_get(v_toApplicative_587_, 3);
v_toSeqRight_594_ = lean_ctor_get(v_toApplicative_587_, 4);
v_isSharedCheck_655_ = !lean_is_exclusive(v_toApplicative_587_);
if (v_isSharedCheck_655_ == 0)
{
lean_object* v_unused_656_; 
v_unused_656_ = lean_ctor_get(v_toApplicative_587_, 1);
lean_dec(v_unused_656_);
v___x_596_ = v_toApplicative_587_;
v_isShared_597_ = v_isSharedCheck_655_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_toSeqRight_594_);
lean_inc(v_toSeqLeft_593_);
lean_inc(v_toSeq_592_);
lean_inc(v_toFunctor_591_);
lean_dec(v_toApplicative_587_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_655_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___f_600_; lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___x_603_; lean_object* v___f_604_; lean_object* v___f_605_; lean_object* v___f_606_; lean_object* v___x_608_; 
v___f_598_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_598_, 0, v_inst_562_);
lean_closure_set(v___f_598_, 1, v_inst_563_);
v___f_599_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_600_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_591_);
v___f_601_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_601_, 0, v_toFunctor_591_);
v___f_602_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_602_, 0, v_toFunctor_591_);
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v___f_601_);
lean_ctor_set(v___x_603_, 1, v___f_602_);
v___f_604_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_604_, 0, v_toSeqRight_594_);
v___f_605_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_605_, 0, v_toSeqLeft_593_);
v___f_606_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_606_, 0, v_toSeq_592_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 4, v___f_604_);
lean_ctor_set(v___x_596_, 3, v___f_605_);
lean_ctor_set(v___x_596_, 2, v___f_606_);
lean_ctor_set(v___x_596_, 1, v___f_599_);
lean_ctor_set(v___x_596_, 0, v___x_603_);
v___x_608_ = v___x_596_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v___f_599_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v___f_606_);
lean_ctor_set(v_reuseFailAlloc_654_, 3, v___f_605_);
lean_ctor_set(v_reuseFailAlloc_654_, 4, v___f_604_);
v___x_608_ = v_reuseFailAlloc_654_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_610_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 1, v___f_600_);
lean_ctor_set(v___x_589_, 0, v___x_608_);
v___x_610_ = v___x_589_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___f_600_);
v___x_610_ = v_reuseFailAlloc_653_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v_map_620_; size_t v_sz_621_; size_t v___x_622_; lean_object* v___x_720__overap_623_; lean_object* v___x_624_; 
v___x_611_ = lean_array_get_size(v_data_564_);
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = lean_unsigned_to_nat(4u);
v___x_614_ = lean_nat_mul(v___x_611_, v___x_613_);
v___x_615_ = lean_unsigned_to_nat(3u);
v___x_616_ = lean_nat_div(v___x_614_, v___x_615_);
lean_dec(v___x_614_);
v___x_617_ = l_Nat_nextPowerOfTwo(v___x_616_);
lean_dec(v___x_616_);
v___x_618_ = lean_box(0);
v___x_619_ = lean_mk_array(v___x_617_, v___x_618_);
v_map_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_map_620_, 0, v___x_612_);
lean_ctor_set(v_map_620_, 1, v___x_619_);
v_sz_621_ = lean_array_size(v_data_564_);
v___x_622_ = ((size_t)0ULL);
v___x_720__overap_623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_610_, v_data_564_, v___f_598_, v_sz_621_, v___x_622_, v_map_620_);
lean_inc(v_a_568_);
lean_inc_ref(v_a_567_);
lean_inc(v_a_566_);
lean_inc_ref(v_a_565_);
v___x_624_ = lean_apply_5(v___x_720__overap_623_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, lean_box(0));
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_644_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_644_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_644_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_644_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v_size_629_; lean_object* v_buckets_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v_size_629_ = lean_ctor_get(v_a_625_, 0);
lean_inc(v_size_629_);
v_buckets_630_ = lean_ctor_get(v_a_625_, 1);
lean_inc_ref(v_buckets_630_);
lean_dec(v_a_625_);
v___x_631_ = lean_mk_empty_array_with_capacity(v_size_629_);
lean_dec(v_size_629_);
v___x_632_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v___x_633_ = lean_array_get_size(v_buckets_630_);
v___x_634_ = lean_nat_dec_lt(v___x_612_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_636_; 
lean_dec_ref(v_buckets_630_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_631_);
v___x_636_ = v___x_627_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
else
{
lean_object* v___f_638_; size_t v___x_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
v___f_638_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__1));
v___x_639_ = lean_usize_of_nat(v___x_633_);
v___x_640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_632_, v___f_638_, v_buckets_630_, v___x_622_, v___x_639_, v___x_631_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_640_);
v___x_642_ = v___x_627_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
v_a_645_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_624_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_624_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___boxed(lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_data_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_659_, v_inst_660_, v_data_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique(lean_object* v_00_u03b1_668_, lean_object* v_inst_669_, lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_data_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_670_, v_inst_671_, v_data_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___boxed(lean_object* v_00_u03b1_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_inst_682_, lean_object* v_data_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Compiler_LCNF_Probe_countUnique(v_00_u03b1_679_, v_inst_680_, v_inst_681_, v_inst_682_, v_data_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec_ref(v_inst_680_);
return v_res_689_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0(lean_object* v_l_690_, lean_object* v_r_691_){
_start:
{
lean_object* v_snd_692_; lean_object* v_snd_693_; uint8_t v___x_694_; 
v_snd_692_ = lean_ctor_get(v_l_690_, 1);
v_snd_693_ = lean_ctor_get(v_r_691_, 1);
v___x_694_ = lean_nat_dec_lt(v_snd_692_, v_snd_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0___boxed(lean_object* v_l_695_, lean_object* v_r_696_){
_start:
{
uint8_t v_res_697_; lean_object* v_r_698_; 
v_res_697_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0(v_l_695_, v_r_696_);
lean_dec_ref(v_r_696_);
lean_dec_ref(v_l_695_);
v_r_698_ = lean_box(v_res_697_);
return v_r_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg(lean_object* v_inst_700_, lean_object* v_inst_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v___f_708_; lean_object* v___x_709_; 
v___f_708_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0));
v___x_709_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_700_, v_inst_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___x_717_; uint8_t v___x_718_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
v___x_711_ = lean_array_get_size(v_a_710_);
v___x_717_ = lean_unsigned_to_nat(0u);
v___x_718_ = lean_nat_dec_eq(v___x_711_, v___x_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___y_722_; uint8_t v___x_724_; 
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_719_ = lean_unsigned_to_nat(1u);
v___x_720_ = lean_nat_sub(v___x_711_, v___x_719_);
v___x_724_ = lean_nat_dec_le(v___x_717_, v___x_720_);
if (v___x_724_ == 0)
{
lean_inc(v___x_720_);
v___y_722_ = v___x_720_;
goto v___jp_721_;
}
else
{
v___y_722_ = v___x_717_;
goto v___jp_721_;
}
v___jp_721_:
{
uint8_t v___x_723_; 
v___x_723_ = lean_nat_dec_le(v___y_722_, v___x_720_);
if (v___x_723_ == 0)
{
lean_dec(v___x_720_);
lean_inc(v___y_722_);
v___y_713_ = v___y_722_;
v___y_714_ = v___y_722_;
goto v___jp_712_;
}
else
{
v___y_713_ = v___y_722_;
v___y_714_ = v___x_720_;
goto v___jp_712_;
}
}
}
else
{
return v___x_709_;
}
v___jp_712_:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_708_, v___x_711_, v_a_710_, v___y_713_, v___y_714_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_714_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
return v___x_716_;
}
}
else
{
return v___x_709_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___boxed(lean_object* v_inst_725_, lean_object* v_inst_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg(v_inst_725_, v_inst_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
lean_dec_ref(v_a_728_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted(lean_object* v_00_u03b1_734_, lean_object* v_inst_735_, lean_object* v_inst_736_, lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v___f_745_; lean_object* v___x_746_; 
v___f_745_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0));
v___x_746_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_736_, v_inst_737_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_748_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___x_754_; uint8_t v___x_755_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
v___x_748_ = lean_array_get_size(v_a_747_);
v___x_754_ = lean_unsigned_to_nat(0u);
v___x_755_ = lean_nat_dec_eq(v___x_748_, v___x_754_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___y_759_; uint8_t v___x_761_; 
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v___x_756_ = lean_unsigned_to_nat(1u);
v___x_757_ = lean_nat_sub(v___x_748_, v___x_756_);
v___x_761_ = lean_nat_dec_le(v___x_754_, v___x_757_);
if (v___x_761_ == 0)
{
lean_inc(v___x_757_);
v___y_759_ = v___x_757_;
goto v___jp_758_;
}
else
{
v___y_759_ = v___x_754_;
goto v___jp_758_;
}
v___jp_758_:
{
uint8_t v___x_760_; 
v___x_760_ = lean_nat_dec_le(v___y_759_, v___x_757_);
if (v___x_760_ == 0)
{
lean_dec(v___x_757_);
lean_inc(v___y_759_);
v___y_750_ = v___y_759_;
v___y_751_ = v___y_759_;
goto v___jp_749_;
}
else
{
v___y_750_ = v___y_759_;
v___y_751_ = v___x_757_;
goto v___jp_749_;
}
}
}
else
{
return v___x_746_;
}
v___jp_749_:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_745_, v___x_748_, v_a_747_, v___y_750_, v___y_751_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_751_);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
}
else
{
return v___x_746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___boxed(lean_object* v_00_u03b1_762_, lean_object* v_inst_763_, lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted(v_00_u03b1_762_, v_inst_763_, v_inst_764_, v_inst_765_, v_inst_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_inst_766_);
lean_dec_ref(v_inst_763_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(uint8_t v_pu_774_, lean_object* v_c_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
switch(lean_obj_tag(v_c_775_))
{
case 0:
{
lean_object* v_decl_782_; lean_object* v_k_783_; lean_object* v___x_784_; lean_object* v_value_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_decl_782_ = lean_ctor_get(v_c_775_, 0);
lean_inc_ref(v_decl_782_);
v_k_783_ = lean_ctor_get(v_c_775_, 1);
lean_inc_ref(v_k_783_);
lean_dec_ref_known(v_c_775_, 2);
v___x_784_ = lean_st_ref_take(v_a_776_);
v_value_785_ = lean_ctor_get(v_decl_782_, 3);
lean_inc(v_value_785_);
lean_dec_ref(v_decl_782_);
v___x_786_ = lean_array_push(v___x_784_, v_value_785_);
v___x_787_ = lean_st_ref_put(v_a_776_, v___x_786_);
v_c_775_ = v_k_783_;
goto _start;
}
case 1:
{
lean_object* v_decl_789_; lean_object* v_k_790_; lean_object* v_value_791_; lean_object* v___x_792_; 
v_decl_789_ = lean_ctor_get(v_c_775_, 0);
lean_inc_ref(v_decl_789_);
v_k_790_ = lean_ctor_get(v_c_775_, 1);
lean_inc_ref(v_k_790_);
lean_dec_ref_known(v_c_775_, 2);
v_value_791_ = lean_ctor_get(v_decl_789_, 4);
lean_inc_ref(v_value_791_);
lean_dec_ref(v_decl_789_);
v___x_792_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_774_, v_value_791_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_dec_ref_known(v___x_792_, 1);
v_c_775_ = v_k_790_;
goto _start;
}
else
{
lean_dec_ref(v_k_790_);
return v___x_792_;
}
}
case 2:
{
lean_object* v_decl_794_; lean_object* v_k_795_; lean_object* v_value_796_; lean_object* v___x_797_; 
v_decl_794_ = lean_ctor_get(v_c_775_, 0);
lean_inc_ref(v_decl_794_);
v_k_795_ = lean_ctor_get(v_c_775_, 1);
lean_inc_ref(v_k_795_);
lean_dec_ref_known(v_c_775_, 2);
v_value_796_ = lean_ctor_get(v_decl_794_, 4);
lean_inc_ref(v_value_796_);
lean_dec_ref(v_decl_794_);
v___x_797_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_774_, v_value_796_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_dec_ref_known(v___x_797_, 1);
v_c_775_ = v_k_795_;
goto _start;
}
else
{
lean_dec_ref(v_k_795_);
return v___x_797_;
}
}
case 4:
{
lean_object* v_cases_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_814_; 
v_cases_799_ = lean_ctor_get(v_c_775_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v_c_775_);
if (v_isSharedCheck_814_ == 0)
{
v___x_801_ = v_c_775_;
v_isShared_802_ = v_isSharedCheck_814_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_cases_799_);
lean_dec(v_c_775_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_814_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v_alts_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v_alts_803_ = lean_ctor_get(v_cases_799_, 3);
lean_inc_ref(v_alts_803_);
lean_dec_ref(v_cases_799_);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = lean_array_get_size(v_alts_803_);
v___x_806_ = lean_box(0);
v___x_807_ = lean_nat_dec_lt(v___x_804_, v___x_805_);
if (v___x_807_ == 0)
{
lean_object* v___x_809_; 
lean_dec_ref(v_alts_803_);
if (v_isShared_802_ == 0)
{
lean_ctor_set_tag(v___x_801_, 0);
lean_ctor_set(v___x_801_, 0, v___x_806_);
v___x_809_ = v___x_801_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_806_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
else
{
size_t v___x_811_; size_t v___x_812_; lean_object* v___x_813_; 
lean_del_object(v___x_801_);
v___x_811_ = ((size_t)0ULL);
v___x_812_ = lean_usize_of_nat(v___x_805_);
v___x_813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_774_, v_alts_803_, v___x_811_, v___x_812_, v___x_806_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
lean_dec_ref(v_alts_803_);
return v___x_813_;
}
}
}
case 7:
{
lean_object* v_k_815_; 
v_k_815_ = lean_ctor_get(v_c_775_, 3);
lean_inc_ref(v_k_815_);
lean_dec_ref_known(v_c_775_, 4);
v_c_775_ = v_k_815_;
goto _start;
}
case 8:
{
lean_object* v_k_817_; 
v_k_817_ = lean_ctor_get(v_c_775_, 3);
lean_inc_ref(v_k_817_);
lean_dec_ref_known(v_c_775_, 4);
v_c_775_ = v_k_817_;
goto _start;
}
case 9:
{
lean_object* v_k_819_; 
v_k_819_ = lean_ctor_get(v_c_775_, 5);
lean_inc_ref(v_k_819_);
lean_dec_ref_known(v_c_775_, 6);
v_c_775_ = v_k_819_;
goto _start;
}
case 10:
{
lean_object* v_k_821_; 
v_k_821_ = lean_ctor_get(v_c_775_, 2);
lean_inc_ref(v_k_821_);
lean_dec_ref_known(v_c_775_, 3);
v_c_775_ = v_k_821_;
goto _start;
}
case 11:
{
lean_object* v_k_823_; 
v_k_823_ = lean_ctor_get(v_c_775_, 2);
lean_inc_ref(v_k_823_);
lean_dec_ref_known(v_c_775_, 3);
v_c_775_ = v_k_823_;
goto _start;
}
case 12:
{
lean_object* v_k_825_; 
v_k_825_ = lean_ctor_get(v_c_775_, 3);
lean_inc_ref(v_k_825_);
lean_dec_ref_known(v_c_775_, 4);
v_c_775_ = v_k_825_;
goto _start;
}
case 13:
{
lean_object* v_k_827_; 
v_k_827_ = lean_ctor_get(v_c_775_, 1);
lean_inc_ref(v_k_827_);
lean_dec_ref_known(v_c_775_, 2);
v_c_775_ = v_k_827_;
goto _start;
}
default: 
{
lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec_ref(v_c_775_);
v___x_829_ = lean_box(0);
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
return v___x_830_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(uint8_t v_pu_831_, lean_object* v_as_832_, size_t v_i_833_, size_t v_stop_834_, lean_object* v_b_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___y_843_; uint8_t v___x_849_; 
v___x_849_ = lean_usize_dec_eq(v_i_833_, v_stop_834_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
v___x_850_ = lean_array_uget_borrowed(v_as_832_, v_i_833_);
switch(lean_obj_tag(v___x_850_))
{
case 0:
{
lean_object* v_code_851_; 
v_code_851_ = lean_ctor_get(v___x_850_, 2);
lean_inc_ref(v_code_851_);
v___y_843_ = v_code_851_;
goto v___jp_842_;
}
case 1:
{
lean_object* v_code_852_; 
v_code_852_ = lean_ctor_get(v___x_850_, 1);
lean_inc_ref(v_code_852_);
v___y_843_ = v_code_852_;
goto v___jp_842_;
}
default: 
{
lean_object* v_code_853_; 
v_code_853_ = lean_ctor_get(v___x_850_, 0);
lean_inc_ref(v_code_853_);
v___y_843_ = v_code_853_;
goto v___jp_842_;
}
}
}
else
{
lean_object* v___x_854_; 
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v_b_835_);
return v___x_854_;
}
v___jp_842_:
{
lean_object* v___x_844_; 
v___x_844_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_831_, v___y_843_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; size_t v___x_846_; size_t v___x_847_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v___x_844_, 1);
v___x_846_ = ((size_t)1ULL);
v___x_847_ = lean_usize_add(v_i_833_, v___x_846_);
v_i_833_ = v___x_847_;
v_b_835_ = v_a_845_;
goto _start;
}
else
{
return v___x_844_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0___boxed(lean_object* v_pu_855_, lean_object* v_as_856_, lean_object* v_i_857_, lean_object* v_stop_858_, lean_object* v_b_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
uint8_t v_pu_boxed_866_; size_t v_i_boxed_867_; size_t v_stop_boxed_868_; lean_object* v_res_869_; 
v_pu_boxed_866_ = lean_unbox(v_pu_855_);
v_i_boxed_867_ = lean_unbox_usize(v_i_857_);
lean_dec(v_i_857_);
v_stop_boxed_868_ = lean_unbox_usize(v_stop_858_);
lean_dec(v_stop_858_);
v_res_869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_boxed_866_, v_as_856_, v_i_boxed_867_, v_stop_boxed_868_, v_b_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v_as_856_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go___boxed(lean_object* v_pu_870_, lean_object* v_c_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
uint8_t v_pu_boxed_878_; lean_object* v_res_879_; 
v_pu_boxed_878_ = lean_unbox(v_pu_870_);
v_res_879_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_boxed_878_, v_c_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(lean_object* v_f_880_, lean_object* v_v_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
if (lean_obj_tag(v_v_881_) == 0)
{
lean_object* v_code_888_; lean_object* v___x_889_; 
v_code_888_ = lean_ctor_get(v_v_881_, 0);
lean_inc_ref(v_code_888_);
lean_dec_ref_known(v_v_881_, 1);
lean_inc(v___y_886_);
lean_inc_ref(v___y_885_);
lean_inc(v___y_884_);
lean_inc_ref(v___y_883_);
lean_inc(v___y_882_);
v___x_889_ = lean_apply_7(v_f_880_, v_code_888_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, lean_box(0));
return v___x_889_;
}
else
{
lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_897_; 
lean_dec_ref(v_f_880_);
v_isSharedCheck_897_ = !lean_is_exclusive(v_v_881_);
if (v_isSharedCheck_897_ == 0)
{
lean_object* v_unused_898_; 
v_unused_898_ = lean_ctor_get(v_v_881_, 0);
lean_dec(v_unused_898_);
v___x_891_ = v_v_881_;
v_isShared_892_ = v_isSharedCheck_897_;
goto v_resetjp_890_;
}
else
{
lean_dec(v_v_881_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_897_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_893_ = lean_box(0);
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 0);
lean_ctor_set(v___x_891_, 0, v___x_893_);
v___x_895_ = v___x_891_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg___boxed(lean_object* v_f_899_, lean_object* v_v_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v_f_899_, v_v_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0(uint8_t v_pu_908_, lean_object* v_f_909_, lean_object* v_v_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v_f_909_, v_v_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___boxed(lean_object* v_pu_918_, lean_object* v_f_919_, lean_object* v_v_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
uint8_t v_pu_boxed_927_; lean_object* v_res_928_; 
v_pu_boxed_927_ = lean_unbox(v_pu_918_);
v_res_928_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0(v_pu_boxed_927_, v_f_919_, v_v_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(uint8_t v_pu_929_, lean_object* v_as_930_, size_t v_i_931_, size_t v_stop_932_, lean_object* v_b_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
uint8_t v___x_940_; 
v___x_940_ = lean_usize_dec_eq(v_i_931_, v_stop_932_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; lean_object* v_value_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_941_ = lean_array_uget_borrowed(v_as_930_, v_i_931_);
v_value_942_ = lean_ctor_get(v___x_941_, 1);
v___x_943_ = lean_box(v_pu_929_);
v___x_944_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go___boxed), 8, 1);
lean_closure_set(v___x_944_, 0, v___x_943_);
lean_inc_ref(v_value_942_);
v___x_945_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v___x_944_, v_value_942_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; size_t v___x_947_; size_t v___x_948_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
lean_dec_ref_known(v___x_945_, 1);
v___x_947_ = ((size_t)1ULL);
v___x_948_ = lean_usize_add(v_i_931_, v___x_947_);
v_i_931_ = v___x_948_;
v_b_933_ = v_a_946_;
goto _start;
}
else
{
return v___x_945_;
}
}
else
{
lean_object* v___x_950_; 
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v_b_933_);
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1___boxed(lean_object* v_pu_951_, lean_object* v_as_952_, lean_object* v_i_953_, lean_object* v_stop_954_, lean_object* v_b_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
uint8_t v_pu_boxed_962_; size_t v_i_boxed_963_; size_t v_stop_boxed_964_; lean_object* v_res_965_; 
v_pu_boxed_962_ = lean_unbox(v_pu_951_);
v_i_boxed_963_ = lean_unbox_usize(v_i_953_);
lean_dec(v_i_953_);
v_stop_boxed_964_ = lean_unbox_usize(v_stop_954_);
lean_dec(v_stop_954_);
v_res_965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_boxed_962_, v_as_952_, v_i_boxed_963_, v_stop_boxed_964_, v_b_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v_as_952_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(uint8_t v_pu_966_, lean_object* v_decls_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_974_ = lean_unsigned_to_nat(0u);
v___x_975_ = lean_array_get_size(v_decls_967_);
v___x_976_ = lean_box(0);
v___x_977_ = lean_nat_dec_lt(v___x_974_, v___x_975_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; 
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
return v___x_978_;
}
else
{
size_t v___x_979_; size_t v___x_980_; lean_object* v___x_981_; 
v___x_979_ = ((size_t)0ULL);
v___x_980_ = lean_usize_of_nat(v___x_975_);
v___x_981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_966_, v_decls_967_, v___x_979_, v___x_980_, v___x_976_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_981_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start___boxed(lean_object* v_pu_982_, lean_object* v_decls_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
uint8_t v_pu_boxed_990_; lean_object* v_res_991_; 
v_pu_boxed_990_ = lean_unbox(v_pu_982_);
v_res_991_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(v_pu_boxed_990_, v_decls_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_decls_983_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getLetValues(uint8_t v_pu_994_, lean_object* v_decls_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_getLetValues___closed__0));
v___x_1002_ = lean_st_mk_ref(v___x_1001_);
v___x_1003_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(v_pu_994_, v_decls_995_, v___x_1002_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1011_; 
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; 
v_unused_1012_ = lean_ctor_get(v___x_1003_, 0);
lean_dec(v_unused_1012_);
v___x_1005_ = v___x_1003_;
v_isShared_1006_ = v_isSharedCheck_1011_;
goto v_resetjp_1004_;
}
else
{
lean_dec(v___x_1003_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1011_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1007_ = lean_st_ref_get(v___x_1002_);
lean_dec(v___x_1002_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1007_);
v___x_1009_ = v___x_1005_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec(v___x_1002_);
v_a_1013_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_1003_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1003_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getLetValues___boxed(lean_object* v_pu_1021_, lean_object* v_decls_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
uint8_t v_pu_boxed_1028_; lean_object* v_res_1029_; 
v_pu_boxed_1028_ = lean_unbox(v_pu_1021_);
v_res_1029_ = l_Lean_Compiler_LCNF_Probe_getLetValues(v_pu_boxed_1028_, v_decls_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec_ref(v_decls_1022_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(uint8_t v_pu_1030_, lean_object* v_code_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
switch(lean_obj_tag(v_code_1031_))
{
case 0:
{
lean_object* v_k_1038_; 
v_k_1038_ = lean_ctor_get(v_code_1031_, 1);
lean_inc_ref(v_k_1038_);
lean_dec_ref_known(v_code_1031_, 2);
v_code_1031_ = v_k_1038_;
goto _start;
}
case 1:
{
lean_object* v_decl_1040_; lean_object* v_k_1041_; lean_object* v_value_1042_; lean_object* v___x_1043_; 
v_decl_1040_ = lean_ctor_get(v_code_1031_, 0);
lean_inc_ref(v_decl_1040_);
v_k_1041_ = lean_ctor_get(v_code_1031_, 1);
lean_inc_ref(v_k_1041_);
lean_dec_ref_known(v_code_1031_, 2);
v_value_1042_ = lean_ctor_get(v_decl_1040_, 4);
lean_inc_ref(v_value_1042_);
lean_dec_ref(v_decl_1040_);
v___x_1043_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1030_, v_value_1042_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_dec_ref_known(v___x_1043_, 1);
v_code_1031_ = v_k_1041_;
goto _start;
}
else
{
lean_dec_ref(v_k_1041_);
return v___x_1043_;
}
}
case 2:
{
lean_object* v_decl_1045_; lean_object* v_k_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v_value_1050_; lean_object* v___x_1051_; 
v_decl_1045_ = lean_ctor_get(v_code_1031_, 0);
lean_inc_ref_n(v_decl_1045_, 2);
v_k_1046_ = lean_ctor_get(v_code_1031_, 1);
lean_inc_ref(v_k_1046_);
lean_dec_ref_known(v_code_1031_, 2);
v___x_1047_ = lean_st_ref_take(v_a_1032_);
v___x_1048_ = lean_array_push(v___x_1047_, v_decl_1045_);
v___x_1049_ = lean_st_ref_put(v_a_1032_, v___x_1048_);
v_value_1050_ = lean_ctor_get(v_decl_1045_, 4);
lean_inc_ref(v_value_1050_);
lean_dec_ref(v_decl_1045_);
v___x_1051_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1030_, v_value_1050_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_dec_ref_known(v___x_1051_, 1);
v_code_1031_ = v_k_1046_;
goto _start;
}
else
{
lean_dec_ref(v_k_1046_);
return v___x_1051_;
}
}
case 4:
{
lean_object* v_cases_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1068_; 
v_cases_1053_ = lean_ctor_get(v_code_1031_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_code_1031_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1055_ = v_code_1031_;
v_isShared_1056_ = v_isSharedCheck_1068_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_cases_1053_);
lean_dec(v_code_1031_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1068_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v_alts_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v_alts_1057_ = lean_ctor_get(v_cases_1053_, 3);
lean_inc_ref(v_alts_1057_);
lean_dec_ref(v_cases_1053_);
v___x_1058_ = lean_unsigned_to_nat(0u);
v___x_1059_ = lean_array_get_size(v_alts_1057_);
v___x_1060_ = lean_box(0);
v___x_1061_ = lean_nat_dec_lt(v___x_1058_, v___x_1059_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1063_; 
lean_dec_ref(v_alts_1057_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set_tag(v___x_1055_, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1060_);
v___x_1063_ = v___x_1055_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1060_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
else
{
size_t v___x_1065_; size_t v___x_1066_; lean_object* v___x_1067_; 
lean_del_object(v___x_1055_);
v___x_1065_ = ((size_t)0ULL);
v___x_1066_ = lean_usize_of_nat(v___x_1059_);
v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_1030_, v_alts_1057_, v___x_1065_, v___x_1066_, v___x_1060_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
lean_dec_ref(v_alts_1057_);
return v___x_1067_;
}
}
}
case 7:
{
lean_object* v_k_1069_; 
v_k_1069_ = lean_ctor_get(v_code_1031_, 3);
lean_inc_ref(v_k_1069_);
lean_dec_ref_known(v_code_1031_, 4);
v_code_1031_ = v_k_1069_;
goto _start;
}
case 8:
{
lean_object* v_k_1071_; 
v_k_1071_ = lean_ctor_get(v_code_1031_, 3);
lean_inc_ref(v_k_1071_);
lean_dec_ref_known(v_code_1031_, 4);
v_code_1031_ = v_k_1071_;
goto _start;
}
case 9:
{
lean_object* v_k_1073_; 
v_k_1073_ = lean_ctor_get(v_code_1031_, 5);
lean_inc_ref(v_k_1073_);
lean_dec_ref_known(v_code_1031_, 6);
v_code_1031_ = v_k_1073_;
goto _start;
}
case 10:
{
lean_object* v_k_1075_; 
v_k_1075_ = lean_ctor_get(v_code_1031_, 2);
lean_inc_ref(v_k_1075_);
lean_dec_ref_known(v_code_1031_, 3);
v_code_1031_ = v_k_1075_;
goto _start;
}
case 11:
{
lean_object* v_k_1077_; 
v_k_1077_ = lean_ctor_get(v_code_1031_, 2);
lean_inc_ref(v_k_1077_);
lean_dec_ref_known(v_code_1031_, 3);
v_code_1031_ = v_k_1077_;
goto _start;
}
case 12:
{
lean_object* v_k_1079_; 
v_k_1079_ = lean_ctor_get(v_code_1031_, 3);
lean_inc_ref(v_k_1079_);
lean_dec_ref_known(v_code_1031_, 4);
v_code_1031_ = v_k_1079_;
goto _start;
}
case 13:
{
lean_object* v_k_1081_; 
v_k_1081_ = lean_ctor_get(v_code_1031_, 1);
lean_inc_ref(v_k_1081_);
lean_dec_ref_known(v_code_1031_, 2);
v_code_1031_ = v_k_1081_;
goto _start;
}
default: 
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec_ref(v_code_1031_);
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(uint8_t v_pu_1085_, lean_object* v_as_1086_, size_t v_i_1087_, size_t v_stop_1088_, lean_object* v_b_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v___y_1097_; uint8_t v___x_1103_; 
v___x_1103_ = lean_usize_dec_eq(v_i_1087_, v_stop_1088_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_array_uget_borrowed(v_as_1086_, v_i_1087_);
switch(lean_obj_tag(v___x_1104_))
{
case 0:
{
lean_object* v_code_1105_; 
v_code_1105_ = lean_ctor_get(v___x_1104_, 2);
lean_inc_ref(v_code_1105_);
v___y_1097_ = v_code_1105_;
goto v___jp_1096_;
}
case 1:
{
lean_object* v_code_1106_; 
v_code_1106_ = lean_ctor_get(v___x_1104_, 1);
lean_inc_ref(v_code_1106_);
v___y_1097_ = v_code_1106_;
goto v___jp_1096_;
}
default: 
{
lean_object* v_code_1107_; 
v_code_1107_ = lean_ctor_get(v___x_1104_, 0);
lean_inc_ref(v_code_1107_);
v___y_1097_ = v_code_1107_;
goto v___jp_1096_;
}
}
}
else
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v_b_1089_);
return v___x_1108_;
}
v___jp_1096_:
{
lean_object* v___x_1098_; 
v___x_1098_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1085_, v___y_1097_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; size_t v___x_1100_; size_t v___x_1101_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___x_1098_, 1);
v___x_1100_ = ((size_t)1ULL);
v___x_1101_ = lean_usize_add(v_i_1087_, v___x_1100_);
v_i_1087_ = v___x_1101_;
v_b_1089_ = v_a_1099_;
goto _start;
}
else
{
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0___boxed(lean_object* v_pu_1109_, lean_object* v_as_1110_, lean_object* v_i_1111_, lean_object* v_stop_1112_, lean_object* v_b_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
uint8_t v_pu_boxed_1120_; size_t v_i_boxed_1121_; size_t v_stop_boxed_1122_; lean_object* v_res_1123_; 
v_pu_boxed_1120_ = lean_unbox(v_pu_1109_);
v_i_boxed_1121_ = lean_unbox_usize(v_i_1111_);
lean_dec(v_i_1111_);
v_stop_boxed_1122_ = lean_unbox_usize(v_stop_1112_);
lean_dec(v_stop_1112_);
v_res_1123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_boxed_1120_, v_as_1110_, v_i_boxed_1121_, v_stop_boxed_1122_, v_b_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v_as_1110_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go___boxed(lean_object* v_pu_1124_, lean_object* v_code_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
uint8_t v_pu_boxed_1132_; lean_object* v_res_1133_; 
v_pu_boxed_1132_ = lean_unbox(v_pu_1124_);
v_res_1133_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_boxed_1132_, v_code_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec(v_a_1126_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(lean_object* v_f_1134_, lean_object* v_v_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
if (lean_obj_tag(v_v_1135_) == 0)
{
lean_object* v_code_1142_; lean_object* v___x_1143_; 
v_code_1142_ = lean_ctor_get(v_v_1135_, 0);
lean_inc_ref(v_code_1142_);
lean_dec_ref_known(v_v_1135_, 1);
lean_inc(v___y_1140_);
lean_inc_ref(v___y_1139_);
lean_inc(v___y_1138_);
lean_inc_ref(v___y_1137_);
lean_inc(v___y_1136_);
v___x_1143_ = lean_apply_7(v_f_1134_, v_code_1142_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, lean_box(0));
return v___x_1143_;
}
else
{
lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1151_; 
lean_dec_ref(v_f_1134_);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_v_1135_);
if (v_isSharedCheck_1151_ == 0)
{
lean_object* v_unused_1152_; 
v_unused_1152_ = lean_ctor_get(v_v_1135_, 0);
lean_dec(v_unused_1152_);
v___x_1145_ = v_v_1135_;
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
else
{
lean_dec(v_v_1135_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1147_ = lean_box(0);
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1147_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg___boxed(lean_object* v_f_1153_, lean_object* v_v_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v_f_1153_, v_v_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0(uint8_t v_pu_1162_, lean_object* v_f_1163_, lean_object* v_v_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v_f_1163_, v_v_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___boxed(lean_object* v_pu_1172_, lean_object* v_f_1173_, lean_object* v_v_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
uint8_t v_pu_boxed_1181_; lean_object* v_res_1182_; 
v_pu_boxed_1181_ = lean_unbox(v_pu_1172_);
v_res_1182_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0(v_pu_boxed_1181_, v_f_1173_, v_v_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(uint8_t v_pu_1183_, lean_object* v_as_1184_, size_t v_i_1185_, size_t v_stop_1186_, lean_object* v_b_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
uint8_t v___x_1194_; 
v___x_1194_ = lean_usize_dec_eq(v_i_1185_, v_stop_1186_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v_value_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1195_ = lean_array_uget_borrowed(v_as_1184_, v_i_1185_);
v_value_1196_ = lean_ctor_get(v___x_1195_, 1);
v___x_1197_ = lean_box(v_pu_1183_);
v___x_1198_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go___boxed), 8, 1);
lean_closure_set(v___x_1198_, 0, v___x_1197_);
lean_inc_ref(v_value_1196_);
v___x_1199_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v___x_1198_, v_value_1196_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; size_t v___x_1201_; size_t v___x_1202_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_a_1200_);
lean_dec_ref_known(v___x_1199_, 1);
v___x_1201_ = ((size_t)1ULL);
v___x_1202_ = lean_usize_add(v_i_1185_, v___x_1201_);
v_i_1185_ = v___x_1202_;
v_b_1187_ = v_a_1200_;
goto _start;
}
else
{
return v___x_1199_;
}
}
else
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v_b_1187_);
return v___x_1204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1___boxed(lean_object* v_pu_1205_, lean_object* v_as_1206_, lean_object* v_i_1207_, lean_object* v_stop_1208_, lean_object* v_b_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
uint8_t v_pu_boxed_1216_; size_t v_i_boxed_1217_; size_t v_stop_boxed_1218_; lean_object* v_res_1219_; 
v_pu_boxed_1216_ = lean_unbox(v_pu_1205_);
v_i_boxed_1217_ = lean_unbox_usize(v_i_1207_);
lean_dec(v_i_1207_);
v_stop_boxed_1218_ = lean_unbox_usize(v_stop_1208_);
lean_dec(v_stop_1208_);
v_res_1219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_boxed_1216_, v_as_1206_, v_i_boxed_1217_, v_stop_boxed_1218_, v_b_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v_as_1206_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(uint8_t v_pu_1220_, lean_object* v_decls_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1228_ = lean_unsigned_to_nat(0u);
v___x_1229_ = lean_array_get_size(v_decls_1221_);
v___x_1230_ = lean_box(0);
v___x_1231_ = lean_nat_dec_lt(v___x_1228_, v___x_1229_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; 
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
return v___x_1232_;
}
else
{
size_t v___x_1233_; size_t v___x_1234_; lean_object* v___x_1235_; 
v___x_1233_ = ((size_t)0ULL);
v___x_1234_ = lean_usize_of_nat(v___x_1229_);
v___x_1235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_1220_, v_decls_1221_, v___x_1233_, v___x_1234_, v___x_1230_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
return v___x_1235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start___boxed(lean_object* v_pu_1236_, lean_object* v_decls_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
uint8_t v_pu_boxed_1244_; lean_object* v_res_1245_; 
v_pu_boxed_1244_ = lean_unbox(v_pu_1236_);
v_res_1245_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(v_pu_boxed_1244_, v_decls_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec_ref(v_decls_1237_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getJps(uint8_t v_pu_1248_, lean_object* v_decls_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_getJps___closed__0));
v___x_1256_ = lean_st_mk_ref(v___x_1255_);
v___x_1257_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(v_pu_1248_, v_decls_1249_, v___x_1256_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1265_; 
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1265_ == 0)
{
lean_object* v_unused_1266_; 
v_unused_1266_ = lean_ctor_get(v___x_1257_, 0);
lean_dec(v_unused_1266_);
v___x_1259_ = v___x_1257_;
v_isShared_1260_ = v_isSharedCheck_1265_;
goto v_resetjp_1258_;
}
else
{
lean_dec(v___x_1257_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1265_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1261_ = lean_st_ref_get(v___x_1256_);
lean_dec(v___x_1256_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1261_);
v___x_1263_ = v___x_1259_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec(v___x_1256_);
v_a_1267_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1257_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1257_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getJps___boxed(lean_object* v_pu_1275_, lean_object* v_decls_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
uint8_t v_pu_boxed_1282_; lean_object* v_res_1283_; 
v_pu_boxed_1282_ = lean_unbox(v_pu_1275_);
v_res_1283_ = l_Lean_Compiler_LCNF_Probe_getJps(v_pu_boxed_1282_, v_decls_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec_ref(v_decls_1276_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(uint8_t v_pu_1284_, lean_object* v_f_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
switch(lean_obj_tag(v_a_1286_))
{
case 0:
{
lean_object* v_decl_1292_; lean_object* v_k_1293_; lean_object* v___x_1294_; 
v_decl_1292_ = lean_ctor_get(v_a_1286_, 0);
lean_inc_ref(v_decl_1292_);
v_k_1293_ = lean_ctor_get(v_a_1286_, 1);
lean_inc_ref(v_k_1293_);
lean_dec_ref_known(v_a_1286_, 2);
lean_inc_ref(v_f_1285_);
lean_inc(v_a_1290_);
lean_inc_ref(v_a_1289_);
lean_inc(v_a_1288_);
lean_inc_ref(v_a_1287_);
v___x_1294_ = lean_apply_6(v_f_1285_, v_decl_1292_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, lean_box(0));
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; uint8_t v___x_1296_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_a_1295_);
v___x_1296_ = lean_unbox(v_a_1295_);
lean_dec(v_a_1295_);
if (v___x_1296_ == 0)
{
lean_dec_ref_known(v___x_1294_, 1);
v_a_1286_ = v_k_1293_;
goto _start;
}
else
{
lean_dec_ref(v_k_1293_);
lean_dec_ref(v_f_1285_);
return v___x_1294_;
}
}
else
{
lean_dec_ref(v_k_1293_);
lean_dec_ref(v_f_1285_);
return v___x_1294_;
}
}
case 1:
{
lean_object* v_decl_1298_; lean_object* v_k_1299_; lean_object* v_value_1300_; lean_object* v___x_1301_; 
v_decl_1298_ = lean_ctor_get(v_a_1286_, 0);
lean_inc_ref(v_decl_1298_);
v_k_1299_ = lean_ctor_get(v_a_1286_, 1);
lean_inc_ref(v_k_1299_);
lean_dec_ref_known(v_a_1286_, 2);
v_value_1300_ = lean_ctor_get(v_decl_1298_, 4);
lean_inc_ref(v_value_1300_);
lean_dec_ref(v_decl_1298_);
lean_inc_ref(v_f_1285_);
v___x_1301_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1284_, v_f_1285_, v_value_1300_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; uint8_t v___x_1303_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v___x_1303_ = lean_unbox(v_a_1302_);
if (v___x_1303_ == 0)
{
lean_dec_ref_known(v___x_1301_, 1);
v_a_1286_ = v_k_1299_;
goto _start;
}
else
{
lean_dec_ref(v_k_1299_);
lean_dec_ref(v_f_1285_);
return v___x_1301_;
}
}
else
{
lean_dec_ref(v_k_1299_);
lean_dec_ref(v_f_1285_);
return v___x_1301_;
}
}
case 2:
{
lean_object* v_decl_1305_; lean_object* v_k_1306_; lean_object* v_value_1307_; lean_object* v___x_1308_; 
v_decl_1305_ = lean_ctor_get(v_a_1286_, 0);
lean_inc_ref(v_decl_1305_);
v_k_1306_ = lean_ctor_get(v_a_1286_, 1);
lean_inc_ref(v_k_1306_);
lean_dec_ref_known(v_a_1286_, 2);
v_value_1307_ = lean_ctor_get(v_decl_1305_, 4);
lean_inc_ref(v_value_1307_);
lean_dec_ref(v_decl_1305_);
lean_inc_ref(v_f_1285_);
v___x_1308_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1284_, v_f_1285_, v_value_1307_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; uint8_t v___x_1310_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v___x_1310_ = lean_unbox(v_a_1309_);
if (v___x_1310_ == 0)
{
lean_dec_ref_known(v___x_1308_, 1);
v_a_1286_ = v_k_1306_;
goto _start;
}
else
{
lean_dec_ref(v_k_1306_);
lean_dec_ref(v_f_1285_);
return v___x_1308_;
}
}
else
{
lean_dec_ref(v_k_1306_);
lean_dec_ref(v_f_1285_);
return v___x_1308_;
}
}
case 4:
{
lean_object* v_cases_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1331_; 
v_cases_1312_ = lean_ctor_get(v_a_1286_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_a_1286_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1314_ = v_a_1286_;
v_isShared_1315_ = v_isSharedCheck_1331_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_cases_1312_);
lean_dec(v_a_1286_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1331_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v_alts_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v_alts_1316_ = lean_ctor_get(v_cases_1312_, 3);
lean_inc_ref(v_alts_1316_);
lean_dec_ref(v_cases_1312_);
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = lean_array_get_size(v_alts_1316_);
v___x_1319_ = lean_nat_dec_lt(v___x_1317_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
lean_dec_ref(v_alts_1316_);
lean_dec_ref(v_f_1285_);
v___x_1320_ = lean_box(v___x_1319_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set_tag(v___x_1314_, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1320_);
v___x_1322_ = v___x_1314_;
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
else
{
if (v___x_1319_ == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1326_; 
lean_dec_ref(v_alts_1316_);
lean_dec_ref(v_f_1285_);
v___x_1324_ = lean_box(v___x_1319_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set_tag(v___x_1314_, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1324_);
v___x_1326_ = v___x_1314_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
else
{
size_t v___x_1328_; size_t v___x_1329_; lean_object* v___x_1330_; 
lean_del_object(v___x_1314_);
v___x_1328_ = ((size_t)0ULL);
v___x_1329_ = lean_usize_of_nat(v___x_1318_);
v___x_1330_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(v_pu_1284_, v_f_1285_, v_alts_1316_, v___x_1328_, v___x_1329_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec_ref(v_alts_1316_);
return v___x_1330_;
}
}
}
}
case 7:
{
lean_object* v_k_1332_; 
v_k_1332_ = lean_ctor_get(v_a_1286_, 3);
lean_inc_ref(v_k_1332_);
lean_dec_ref_known(v_a_1286_, 4);
v_a_1286_ = v_k_1332_;
goto _start;
}
case 8:
{
lean_object* v_k_1334_; 
v_k_1334_ = lean_ctor_get(v_a_1286_, 3);
lean_inc_ref(v_k_1334_);
lean_dec_ref_known(v_a_1286_, 4);
v_a_1286_ = v_k_1334_;
goto _start;
}
case 9:
{
lean_object* v_k_1336_; 
v_k_1336_ = lean_ctor_get(v_a_1286_, 5);
lean_inc_ref(v_k_1336_);
lean_dec_ref_known(v_a_1286_, 6);
v_a_1286_ = v_k_1336_;
goto _start;
}
case 10:
{
lean_object* v_k_1338_; 
v_k_1338_ = lean_ctor_get(v_a_1286_, 2);
lean_inc_ref(v_k_1338_);
lean_dec_ref_known(v_a_1286_, 3);
v_a_1286_ = v_k_1338_;
goto _start;
}
case 11:
{
lean_object* v_k_1340_; 
v_k_1340_ = lean_ctor_get(v_a_1286_, 2);
lean_inc_ref(v_k_1340_);
lean_dec_ref_known(v_a_1286_, 3);
v_a_1286_ = v_k_1340_;
goto _start;
}
case 12:
{
lean_object* v_k_1342_; 
v_k_1342_ = lean_ctor_get(v_a_1286_, 3);
lean_inc_ref(v_k_1342_);
lean_dec_ref_known(v_a_1286_, 4);
v_a_1286_ = v_k_1342_;
goto _start;
}
case 13:
{
lean_object* v_k_1344_; 
v_k_1344_ = lean_ctor_get(v_a_1286_, 1);
lean_inc_ref(v_k_1344_);
lean_dec_ref_known(v_a_1286_, 2);
v_a_1286_ = v_k_1344_;
goto _start;
}
default: 
{
uint8_t v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_dec_ref(v_a_1286_);
lean_dec_ref(v_f_1285_);
v___x_1346_ = 0;
v___x_1347_ = lean_box(v___x_1346_);
v___x_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
return v___x_1348_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(uint8_t v_pu_1349_, lean_object* v_f_1350_, lean_object* v_as_1351_, size_t v_i_1352_, size_t v_stop_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
uint8_t v___x_1359_; 
v___x_1359_ = lean_usize_dec_eq(v_i_1352_, v_stop_1353_);
if (v___x_1359_ == 0)
{
uint8_t v___x_1360_; lean_object* v___y_1362_; lean_object* v___x_1377_; 
v___x_1360_ = 1;
v___x_1377_ = lean_array_uget_borrowed(v_as_1351_, v_i_1352_);
switch(lean_obj_tag(v___x_1377_))
{
case 0:
{
lean_object* v_code_1378_; 
v_code_1378_ = lean_ctor_get(v___x_1377_, 2);
lean_inc_ref(v_code_1378_);
v___y_1362_ = v_code_1378_;
goto v___jp_1361_;
}
case 1:
{
lean_object* v_code_1379_; 
v_code_1379_ = lean_ctor_get(v___x_1377_, 1);
lean_inc_ref(v_code_1379_);
v___y_1362_ = v_code_1379_;
goto v___jp_1361_;
}
default: 
{
lean_object* v_code_1380_; 
v_code_1380_ = lean_ctor_get(v___x_1377_, 0);
lean_inc_ref(v_code_1380_);
v___y_1362_ = v_code_1380_;
goto v___jp_1361_;
}
}
v___jp_1361_:
{
lean_object* v___x_1363_; 
lean_inc_ref(v_f_1350_);
v___x_1363_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1349_, v_f_1350_, v___y_1362_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1376_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1376_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1376_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
uint8_t v___x_1368_; 
v___x_1368_ = lean_unbox(v_a_1364_);
lean_dec(v_a_1364_);
if (v___x_1368_ == 0)
{
size_t v___x_1369_; size_t v___x_1370_; 
lean_del_object(v___x_1366_);
v___x_1369_ = ((size_t)1ULL);
v___x_1370_ = lean_usize_add(v_i_1352_, v___x_1369_);
v_i_1352_ = v___x_1370_;
goto _start;
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
lean_dec_ref(v_f_1350_);
v___x_1372_ = lean_box(v___x_1360_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1372_);
v___x_1374_ = v___x_1366_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
else
{
lean_dec_ref(v_f_1350_);
return v___x_1363_;
}
}
}
else
{
uint8_t v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec_ref(v_f_1350_);
v___x_1381_ = 0;
v___x_1382_ = lean_box(v___x_1381_);
v___x_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
return v___x_1383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0___boxed(lean_object* v_pu_1384_, lean_object* v_f_1385_, lean_object* v_as_1386_, lean_object* v_i_1387_, lean_object* v_stop_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
uint8_t v_pu_boxed_1394_; size_t v_i_boxed_1395_; size_t v_stop_boxed_1396_; lean_object* v_res_1397_; 
v_pu_boxed_1394_ = lean_unbox(v_pu_1384_);
v_i_boxed_1395_ = lean_unbox_usize(v_i_1387_);
lean_dec(v_i_1387_);
v_stop_boxed_1396_ = lean_unbox_usize(v_stop_1388_);
lean_dec(v_stop_1388_);
v_res_1397_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(v_pu_boxed_1394_, v_f_1385_, v_as_1386_, v_i_boxed_1395_, v_stop_boxed_1396_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec_ref(v_as_1386_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go___boxed(lean_object* v_pu_1398_, lean_object* v_f_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_){
_start:
{
uint8_t v_pu_boxed_1406_; lean_object* v_res_1407_; 
v_pu_boxed_1406_ = lean_unbox(v_pu_1398_);
v_res_1407_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_boxed_1406_, v_f_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(lean_object* v_v_1408_, lean_object* v_f_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
if (lean_obj_tag(v_v_1408_) == 0)
{
lean_object* v_code_1415_; lean_object* v___x_1416_; 
v_code_1415_ = lean_ctor_get(v_v_1408_, 0);
lean_inc_ref(v_code_1415_);
lean_dec_ref_known(v_v_1408_, 1);
lean_inc(v___y_1413_);
lean_inc_ref(v___y_1412_);
lean_inc(v___y_1411_);
lean_inc_ref(v___y_1410_);
v___x_1416_ = lean_apply_6(v_f_1409_, v_code_1415_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, lean_box(0));
return v___x_1416_;
}
else
{
lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1425_; 
lean_dec_ref(v_f_1409_);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_v_1408_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; 
v_unused_1426_ = lean_ctor_get(v_v_1408_, 0);
lean_dec(v_unused_1426_);
v___x_1418_ = v_v_1408_;
v_isShared_1419_ = v_isSharedCheck_1425_;
goto v_resetjp_1417_;
}
else
{
lean_dec(v_v_1408_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1425_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
uint8_t v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1420_ = 0;
v___x_1421_ = lean_box(v___x_1420_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set_tag(v___x_1418_, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1421_);
v___x_1423_ = v___x_1418_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg___boxed(lean_object* v_v_1427_, lean_object* v_f_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_v_1427_, v_f_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0(uint8_t v_pu_1435_, lean_object* v_v_1436_, lean_object* v_f_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_v_1436_, v_f_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___boxed(lean_object* v_pu_1444_, lean_object* v_v_1445_, lean_object* v_f_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
uint8_t v_pu_boxed_1452_; lean_object* v_res_1453_; 
v_pu_boxed_1452_ = lean_unbox(v_pu_1444_);
v_res_1453_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0(v_pu_boxed_1452_, v_v_1445_, v_f_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(uint8_t v_pu_1454_, lean_object* v_f_1455_, lean_object* v_as_1456_, size_t v_i_1457_, size_t v_stop_1458_, lean_object* v_b_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_a_1466_; uint8_t v___x_1470_; 
v___x_1470_ = lean_usize_dec_eq(v_i_1457_, v_stop_1458_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; lean_object* v_value_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1471_ = lean_array_uget_borrowed(v_as_1456_, v_i_1457_);
v_value_1472_ = lean_ctor_get(v___x_1471_, 1);
v___x_1473_ = lean_box(v_pu_1454_);
lean_inc_ref(v_f_1455_);
v___x_1474_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go___boxed), 8, 2);
lean_closure_set(v___x_1474_, 0, v___x_1473_);
lean_closure_set(v___x_1474_, 1, v_f_1455_);
lean_inc_ref(v_value_1472_);
v___x_1475_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_1472_, v___x_1474_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; uint8_t v___x_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
v___x_1477_ = lean_unbox(v_a_1476_);
lean_dec(v_a_1476_);
if (v___x_1477_ == 0)
{
v_a_1466_ = v_b_1459_;
goto v___jp_1465_;
}
else
{
lean_object* v___x_1478_; 
lean_inc(v___x_1471_);
v___x_1478_ = lean_array_push(v_b_1459_, v___x_1471_);
v_a_1466_ = v___x_1478_;
goto v___jp_1465_;
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec_ref(v_b_1459_);
lean_dec_ref(v_f_1455_);
v_a_1479_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1475_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1475_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
else
{
lean_object* v___x_1487_; 
lean_dec_ref(v_f_1455_);
v___x_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1487_, 0, v_b_1459_);
return v___x_1487_;
}
v___jp_1465_:
{
size_t v___x_1467_; size_t v___x_1468_; 
v___x_1467_ = ((size_t)1ULL);
v___x_1468_ = lean_usize_add(v_i_1457_, v___x_1467_);
v_i_1457_ = v___x_1468_;
v_b_1459_ = v_a_1466_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1___boxed(lean_object* v_pu_1488_, lean_object* v_f_1489_, lean_object* v_as_1490_, lean_object* v_i_1491_, lean_object* v_stop_1492_, lean_object* v_b_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
uint8_t v_pu_boxed_1499_; size_t v_i_boxed_1500_; size_t v_stop_boxed_1501_; lean_object* v_res_1502_; 
v_pu_boxed_1499_ = lean_unbox(v_pu_1488_);
v_i_boxed_1500_ = lean_unbox_usize(v_i_1491_);
lean_dec(v_i_1491_);
v_stop_boxed_1501_ = lean_unbox_usize(v_stop_1492_);
lean_dec(v_stop_1492_);
v_res_1502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_boxed_1499_, v_f_1489_, v_as_1490_, v_i_boxed_1500_, v_stop_boxed_1501_, v_b_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec_ref(v_as_1490_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByLet(uint8_t v_pu_1505_, lean_object* v_f_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1513_ = lean_unsigned_to_nat(0u);
v___x_1514_ = lean_array_get_size(v_a_1507_);
v___x_1515_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_1516_ = lean_nat_dec_lt(v___x_1513_, v___x_1514_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; 
lean_dec_ref(v_f_1506_);
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1515_);
return v___x_1517_;
}
else
{
size_t v___x_1518_; size_t v___x_1519_; lean_object* v___x_1520_; 
v___x_1518_ = ((size_t)0ULL);
v___x_1519_ = lean_usize_of_nat(v___x_1514_);
v___x_1520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_1505_, v_f_1506_, v_a_1507_, v___x_1518_, v___x_1519_, v___x_1515_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_);
return v___x_1520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByLet___boxed(lean_object* v_pu_1521_, lean_object* v_f_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
uint8_t v_pu_boxed_1529_; lean_object* v_res_1530_; 
v_pu_boxed_1529_ = lean_unbox(v_pu_1521_);
v_res_1530_ = l_Lean_Compiler_LCNF_Probe_filterByLet(v_pu_boxed_1529_, v_f_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
lean_dec_ref(v_a_1523_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(uint8_t v_pu_1531_, lean_object* v_f_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
switch(lean_obj_tag(v_a_1533_))
{
case 0:
{
lean_object* v_k_1539_; 
v_k_1539_ = lean_ctor_get(v_a_1533_, 1);
lean_inc_ref(v_k_1539_);
lean_dec_ref_known(v_a_1533_, 2);
v_a_1533_ = v_k_1539_;
goto _start;
}
case 1:
{
lean_object* v_decl_1541_; lean_object* v_k_1542_; lean_object* v___x_1543_; 
v_decl_1541_ = lean_ctor_get(v_a_1533_, 0);
lean_inc_ref_n(v_decl_1541_, 2);
v_k_1542_ = lean_ctor_get(v_a_1533_, 1);
lean_inc_ref(v_k_1542_);
lean_dec_ref_known(v_a_1533_, 2);
lean_inc_ref(v_f_1532_);
lean_inc(v_a_1537_);
lean_inc_ref(v_a_1536_);
lean_inc(v_a_1535_);
lean_inc_ref(v_a_1534_);
v___x_1543_ = lean_apply_6(v_f_1532_, v_decl_1541_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, lean_box(0));
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; uint8_t v___x_1545_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1544_);
v___x_1545_ = lean_unbox(v_a_1544_);
lean_dec(v_a_1544_);
if (v___x_1545_ == 0)
{
lean_object* v_value_1546_; lean_object* v___x_1547_; 
lean_dec_ref_known(v___x_1543_, 1);
v_value_1546_ = lean_ctor_get(v_decl_1541_, 4);
lean_inc_ref(v_value_1546_);
lean_dec_ref(v_decl_1541_);
lean_inc_ref(v_f_1532_);
v___x_1547_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_1531_, v_f_1532_, v_value_1546_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; uint8_t v___x_1549_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v___x_1549_ = lean_unbox(v_a_1548_);
if (v___x_1549_ == 0)
{
lean_dec_ref_known(v___x_1547_, 1);
v_a_1533_ = v_k_1542_;
goto _start;
}
else
{
lean_dec_ref(v_k_1542_);
lean_dec_ref(v_f_1532_);
return v___x_1547_;
}
}
else
{
lean_dec_ref(v_k_1542_);
lean_dec_ref(v_f_1532_);
return v___x_1547_;
}
}
else
{
lean_dec_ref(v_k_1542_);
lean_dec_ref(v_decl_1541_);
lean_dec_ref(v_f_1532_);
return v___x_1543_;
}
}
else
{
lean_dec_ref(v_k_1542_);
lean_dec_ref(v_decl_1541_);
lean_dec_ref(v_f_1532_);
return v___x_1543_;
}
}
case 2:
{
lean_object* v_k_1551_; 
v_k_1551_ = lean_ctor_get(v_a_1533_, 1);
lean_inc_ref(v_k_1551_);
lean_dec_ref_known(v_a_1533_, 2);
v_a_1533_ = v_k_1551_;
goto _start;
}
case 4:
{
lean_object* v_cases_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1572_; 
v_cases_1553_ = lean_ctor_get(v_a_1533_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_a_1533_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1555_ = v_a_1533_;
v_isShared_1556_ = v_isSharedCheck_1572_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_cases_1553_);
lean_dec(v_a_1533_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1572_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v_alts_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v_alts_1557_ = lean_ctor_get(v_cases_1553_, 3);
lean_inc_ref(v_alts_1557_);
lean_dec_ref(v_cases_1553_);
v___x_1558_ = lean_unsigned_to_nat(0u);
v___x_1559_ = lean_array_get_size(v_alts_1557_);
v___x_1560_ = lean_nat_dec_lt(v___x_1558_, v___x_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; lean_object* v___x_1563_; 
lean_dec_ref(v_alts_1557_);
lean_dec_ref(v_f_1532_);
v___x_1561_ = lean_box(v___x_1560_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set_tag(v___x_1555_, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1561_);
v___x_1563_ = v___x_1555_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
else
{
if (v___x_1560_ == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1567_; 
lean_dec_ref(v_alts_1557_);
lean_dec_ref(v_f_1532_);
v___x_1565_ = lean_box(v___x_1560_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set_tag(v___x_1555_, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1565_);
v___x_1567_ = v___x_1555_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
else
{
size_t v___x_1569_; size_t v___x_1570_; lean_object* v___x_1571_; 
lean_del_object(v___x_1555_);
v___x_1569_ = ((size_t)0ULL);
v___x_1570_ = lean_usize_of_nat(v___x_1559_);
v___x_1571_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(v_pu_1531_, v_f_1532_, v_alts_1557_, v___x_1569_, v___x_1570_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
lean_dec_ref(v_alts_1557_);
return v___x_1571_;
}
}
}
}
case 7:
{
lean_object* v_k_1573_; 
v_k_1573_ = lean_ctor_get(v_a_1533_, 3);
lean_inc_ref(v_k_1573_);
lean_dec_ref_known(v_a_1533_, 4);
v_a_1533_ = v_k_1573_;
goto _start;
}
case 8:
{
lean_object* v_k_1575_; 
v_k_1575_ = lean_ctor_get(v_a_1533_, 3);
lean_inc_ref(v_k_1575_);
lean_dec_ref_known(v_a_1533_, 4);
v_a_1533_ = v_k_1575_;
goto _start;
}
case 9:
{
lean_object* v_k_1577_; 
v_k_1577_ = lean_ctor_get(v_a_1533_, 5);
lean_inc_ref(v_k_1577_);
lean_dec_ref_known(v_a_1533_, 6);
v_a_1533_ = v_k_1577_;
goto _start;
}
case 10:
{
lean_object* v_k_1579_; 
v_k_1579_ = lean_ctor_get(v_a_1533_, 2);
lean_inc_ref(v_k_1579_);
lean_dec_ref_known(v_a_1533_, 3);
v_a_1533_ = v_k_1579_;
goto _start;
}
case 11:
{
lean_object* v_k_1581_; 
v_k_1581_ = lean_ctor_get(v_a_1533_, 2);
lean_inc_ref(v_k_1581_);
lean_dec_ref_known(v_a_1533_, 3);
v_a_1533_ = v_k_1581_;
goto _start;
}
case 12:
{
lean_object* v_k_1583_; 
v_k_1583_ = lean_ctor_get(v_a_1533_, 3);
lean_inc_ref(v_k_1583_);
lean_dec_ref_known(v_a_1533_, 4);
v_a_1533_ = v_k_1583_;
goto _start;
}
case 13:
{
lean_object* v_k_1585_; 
v_k_1585_ = lean_ctor_get(v_a_1533_, 1);
lean_inc_ref(v_k_1585_);
lean_dec_ref_known(v_a_1533_, 2);
v_a_1533_ = v_k_1585_;
goto _start;
}
default: 
{
uint8_t v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_dec_ref(v_a_1533_);
lean_dec_ref(v_f_1532_);
v___x_1587_ = 0;
v___x_1588_ = lean_box(v___x_1587_);
v___x_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
return v___x_1589_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(uint8_t v_pu_1590_, lean_object* v_f_1591_, lean_object* v_as_1592_, size_t v_i_1593_, size_t v_stop_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
uint8_t v___x_1600_; 
v___x_1600_ = lean_usize_dec_eq(v_i_1593_, v_stop_1594_);
if (v___x_1600_ == 0)
{
uint8_t v___x_1601_; lean_object* v___y_1603_; lean_object* v___x_1618_; 
v___x_1601_ = 1;
v___x_1618_ = lean_array_uget_borrowed(v_as_1592_, v_i_1593_);
switch(lean_obj_tag(v___x_1618_))
{
case 0:
{
lean_object* v_code_1619_; 
v_code_1619_ = lean_ctor_get(v___x_1618_, 2);
lean_inc_ref(v_code_1619_);
v___y_1603_ = v_code_1619_;
goto v___jp_1602_;
}
case 1:
{
lean_object* v_code_1620_; 
v_code_1620_ = lean_ctor_get(v___x_1618_, 1);
lean_inc_ref(v_code_1620_);
v___y_1603_ = v_code_1620_;
goto v___jp_1602_;
}
default: 
{
lean_object* v_code_1621_; 
v_code_1621_ = lean_ctor_get(v___x_1618_, 0);
lean_inc_ref(v_code_1621_);
v___y_1603_ = v_code_1621_;
goto v___jp_1602_;
}
}
v___jp_1602_:
{
lean_object* v___x_1604_; 
lean_inc_ref(v_f_1591_);
v___x_1604_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_1590_, v_f_1591_, v___y_1603_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1617_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1607_ = v___x_1604_;
v_isShared_1608_ = v_isSharedCheck_1617_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1604_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1617_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
uint8_t v___x_1609_; 
v___x_1609_ = lean_unbox(v_a_1605_);
lean_dec(v_a_1605_);
if (v___x_1609_ == 0)
{
size_t v___x_1610_; size_t v___x_1611_; 
lean_del_object(v___x_1607_);
v___x_1610_ = ((size_t)1ULL);
v___x_1611_ = lean_usize_add(v_i_1593_, v___x_1610_);
v_i_1593_ = v___x_1611_;
goto _start;
}
else
{
lean_object* v___x_1613_; lean_object* v___x_1615_; 
lean_dec_ref(v_f_1591_);
v___x_1613_ = lean_box(v___x_1601_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v___x_1613_);
v___x_1615_ = v___x_1607_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
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
lean_dec_ref(v_f_1591_);
return v___x_1604_;
}
}
}
else
{
uint8_t v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
lean_dec_ref(v_f_1591_);
v___x_1622_ = 0;
v___x_1623_ = lean_box(v___x_1622_);
v___x_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
return v___x_1624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0___boxed(lean_object* v_pu_1625_, lean_object* v_f_1626_, lean_object* v_as_1627_, lean_object* v_i_1628_, lean_object* v_stop_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
uint8_t v_pu_boxed_1635_; size_t v_i_boxed_1636_; size_t v_stop_boxed_1637_; lean_object* v_res_1638_; 
v_pu_boxed_1635_ = lean_unbox(v_pu_1625_);
v_i_boxed_1636_ = lean_unbox_usize(v_i_1628_);
lean_dec(v_i_1628_);
v_stop_boxed_1637_ = lean_unbox_usize(v_stop_1629_);
lean_dec(v_stop_1629_);
v_res_1638_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(v_pu_boxed_1635_, v_f_1626_, v_as_1627_, v_i_boxed_1636_, v_stop_boxed_1637_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec_ref(v_as_1627_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go___boxed(lean_object* v_pu_1639_, lean_object* v_f_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
uint8_t v_pu_boxed_1647_; lean_object* v_res_1648_; 
v_pu_boxed_1647_ = lean_unbox(v_pu_1639_);
v_res_1648_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_boxed_1647_, v_f_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(uint8_t v_pu_1649_, lean_object* v_f_1650_, lean_object* v_as_1651_, size_t v_i_1652_, size_t v_stop_1653_, lean_object* v_b_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_a_1661_; uint8_t v___x_1665_; 
v___x_1665_ = lean_usize_dec_eq(v_i_1652_, v_stop_1653_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; lean_object* v_value_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1666_ = lean_array_uget_borrowed(v_as_1651_, v_i_1652_);
v_value_1667_ = lean_ctor_get(v___x_1666_, 1);
v___x_1668_ = lean_box(v_pu_1649_);
lean_inc_ref(v_f_1650_);
v___x_1669_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go___boxed), 8, 2);
lean_closure_set(v___x_1669_, 0, v___x_1668_);
lean_closure_set(v___x_1669_, 1, v_f_1650_);
lean_inc_ref(v_value_1667_);
v___x_1670_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_1667_, v___x_1669_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; uint8_t v___x_1672_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref_known(v___x_1670_, 1);
v___x_1672_ = lean_unbox(v_a_1671_);
lean_dec(v_a_1671_);
if (v___x_1672_ == 0)
{
v_a_1661_ = v_b_1654_;
goto v___jp_1660_;
}
else
{
lean_object* v___x_1673_; 
lean_inc(v___x_1666_);
v___x_1673_ = lean_array_push(v_b_1654_, v___x_1666_);
v_a_1661_ = v___x_1673_;
goto v___jp_1660_;
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_dec_ref(v_b_1654_);
lean_dec_ref(v_f_1650_);
v_a_1674_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1670_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1670_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
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
lean_object* v___x_1682_; 
lean_dec_ref(v_f_1650_);
v___x_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1682_, 0, v_b_1654_);
return v___x_1682_;
}
v___jp_1660_:
{
size_t v___x_1662_; size_t v___x_1663_; 
v___x_1662_ = ((size_t)1ULL);
v___x_1663_ = lean_usize_add(v_i_1652_, v___x_1662_);
v_i_1652_ = v___x_1663_;
v_b_1654_ = v_a_1661_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0___boxed(lean_object* v_pu_1683_, lean_object* v_f_1684_, lean_object* v_as_1685_, lean_object* v_i_1686_, lean_object* v_stop_1687_, lean_object* v_b_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
uint8_t v_pu_boxed_1694_; size_t v_i_boxed_1695_; size_t v_stop_boxed_1696_; lean_object* v_res_1697_; 
v_pu_boxed_1694_ = lean_unbox(v_pu_1683_);
v_i_boxed_1695_ = lean_unbox_usize(v_i_1686_);
lean_dec(v_i_1686_);
v_stop_boxed_1696_ = lean_unbox_usize(v_stop_1687_);
lean_dec(v_stop_1687_);
v_res_1697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_boxed_1694_, v_f_1684_, v_as_1685_, v_i_boxed_1695_, v_stop_boxed_1696_, v_b_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec_ref(v_as_1685_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFun(uint8_t v_pu_1698_, lean_object* v_f_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1706_ = lean_unsigned_to_nat(0u);
v___x_1707_ = lean_array_get_size(v_a_1700_);
v___x_1708_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_1709_ = lean_nat_dec_lt(v___x_1706_, v___x_1707_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; 
lean_dec_ref(v_f_1699_);
v___x_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1708_);
return v___x_1710_;
}
else
{
size_t v___x_1711_; size_t v___x_1712_; lean_object* v___x_1713_; 
v___x_1711_ = ((size_t)0ULL);
v___x_1712_ = lean_usize_of_nat(v___x_1707_);
v___x_1713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_1698_, v_f_1699_, v_a_1700_, v___x_1711_, v___x_1712_, v___x_1708_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
return v___x_1713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFun___boxed(lean_object* v_pu_1714_, lean_object* v_f_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_){
_start:
{
uint8_t v_pu_boxed_1722_; lean_object* v_res_1723_; 
v_pu_boxed_1722_ = lean_unbox(v_pu_1714_);
v_res_1723_ = l_Lean_Compiler_LCNF_Probe_filterByFun(v_pu_boxed_1722_, v_f_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_);
lean_dec(v_a_1720_);
lean_dec_ref(v_a_1719_);
lean_dec(v_a_1718_);
lean_dec_ref(v_a_1717_);
lean_dec_ref(v_a_1716_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(uint8_t v_pu_1724_, lean_object* v_f_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
switch(lean_obj_tag(v_a_1726_))
{
case 0:
{
lean_object* v_k_1732_; 
v_k_1732_ = lean_ctor_get(v_a_1726_, 1);
lean_inc_ref(v_k_1732_);
lean_dec_ref_known(v_a_1726_, 2);
v_a_1726_ = v_k_1732_;
goto _start;
}
case 1:
{
lean_object* v_decl_1734_; lean_object* v_k_1735_; lean_object* v_value_1736_; lean_object* v___x_1737_; 
v_decl_1734_ = lean_ctor_get(v_a_1726_, 0);
lean_inc_ref(v_decl_1734_);
v_k_1735_ = lean_ctor_get(v_a_1726_, 1);
lean_inc_ref(v_k_1735_);
lean_dec_ref_known(v_a_1726_, 2);
v_value_1736_ = lean_ctor_get(v_decl_1734_, 4);
lean_inc_ref(v_value_1736_);
lean_dec_ref(v_decl_1734_);
lean_inc_ref(v_f_1725_);
v___x_1737_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1724_, v_f_1725_, v_value_1736_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; uint8_t v___x_1739_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v___x_1739_ = lean_unbox(v_a_1738_);
if (v___x_1739_ == 0)
{
lean_dec_ref_known(v___x_1737_, 1);
v_a_1726_ = v_k_1735_;
goto _start;
}
else
{
lean_dec_ref(v_k_1735_);
lean_dec_ref(v_f_1725_);
return v___x_1737_;
}
}
else
{
lean_dec_ref(v_k_1735_);
lean_dec_ref(v_f_1725_);
return v___x_1737_;
}
}
case 2:
{
lean_object* v_decl_1741_; lean_object* v_k_1742_; lean_object* v___x_1743_; 
v_decl_1741_ = lean_ctor_get(v_a_1726_, 0);
lean_inc_ref_n(v_decl_1741_, 2);
v_k_1742_ = lean_ctor_get(v_a_1726_, 1);
lean_inc_ref(v_k_1742_);
lean_dec_ref_known(v_a_1726_, 2);
lean_inc_ref(v_f_1725_);
lean_inc(v_a_1730_);
lean_inc_ref(v_a_1729_);
lean_inc(v_a_1728_);
lean_inc_ref(v_a_1727_);
v___x_1743_ = lean_apply_6(v_f_1725_, v_decl_1741_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, lean_box(0));
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; uint8_t v___x_1745_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1744_);
v___x_1745_ = lean_unbox(v_a_1744_);
lean_dec(v_a_1744_);
if (v___x_1745_ == 0)
{
lean_object* v_value_1746_; lean_object* v___x_1747_; 
lean_dec_ref_known(v___x_1743_, 1);
v_value_1746_ = lean_ctor_get(v_decl_1741_, 4);
lean_inc_ref(v_value_1746_);
lean_dec_ref(v_decl_1741_);
lean_inc_ref(v_f_1725_);
v___x_1747_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1724_, v_f_1725_, v_value_1746_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; uint8_t v___x_1749_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
v___x_1749_ = lean_unbox(v_a_1748_);
if (v___x_1749_ == 0)
{
lean_dec_ref_known(v___x_1747_, 1);
v_a_1726_ = v_k_1742_;
goto _start;
}
else
{
lean_dec_ref(v_k_1742_);
lean_dec_ref(v_f_1725_);
return v___x_1747_;
}
}
else
{
lean_dec_ref(v_k_1742_);
lean_dec_ref(v_f_1725_);
return v___x_1747_;
}
}
else
{
lean_dec_ref(v_k_1742_);
lean_dec_ref(v_decl_1741_);
lean_dec_ref(v_f_1725_);
return v___x_1743_;
}
}
else
{
lean_dec_ref(v_k_1742_);
lean_dec_ref(v_decl_1741_);
lean_dec_ref(v_f_1725_);
return v___x_1743_;
}
}
case 4:
{
lean_object* v_cases_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1770_; 
v_cases_1751_ = lean_ctor_get(v_a_1726_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v_a_1726_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1753_ = v_a_1726_;
v_isShared_1754_ = v_isSharedCheck_1770_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_cases_1751_);
lean_dec(v_a_1726_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1770_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v_alts_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v_alts_1755_ = lean_ctor_get(v_cases_1751_, 3);
lean_inc_ref(v_alts_1755_);
lean_dec_ref(v_cases_1751_);
v___x_1756_ = lean_unsigned_to_nat(0u);
v___x_1757_ = lean_array_get_size(v_alts_1755_);
v___x_1758_ = lean_nat_dec_lt(v___x_1756_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
lean_dec_ref(v_alts_1755_);
lean_dec_ref(v_f_1725_);
v___x_1759_ = lean_box(v___x_1758_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set_tag(v___x_1753_, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1759_);
v___x_1761_ = v___x_1753_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
else
{
if (v___x_1758_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1765_; 
lean_dec_ref(v_alts_1755_);
lean_dec_ref(v_f_1725_);
v___x_1763_ = lean_box(v___x_1758_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set_tag(v___x_1753_, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1763_);
v___x_1765_ = v___x_1753_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
else
{
size_t v___x_1767_; size_t v___x_1768_; lean_object* v___x_1769_; 
lean_del_object(v___x_1753_);
v___x_1767_ = ((size_t)0ULL);
v___x_1768_ = lean_usize_of_nat(v___x_1757_);
v___x_1769_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(v_pu_1724_, v_f_1725_, v_alts_1755_, v___x_1767_, v___x_1768_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
lean_dec_ref(v_alts_1755_);
return v___x_1769_;
}
}
}
}
case 7:
{
lean_object* v_k_1771_; 
v_k_1771_ = lean_ctor_get(v_a_1726_, 3);
lean_inc_ref(v_k_1771_);
lean_dec_ref_known(v_a_1726_, 4);
v_a_1726_ = v_k_1771_;
goto _start;
}
case 8:
{
lean_object* v_k_1773_; 
v_k_1773_ = lean_ctor_get(v_a_1726_, 3);
lean_inc_ref(v_k_1773_);
lean_dec_ref_known(v_a_1726_, 4);
v_a_1726_ = v_k_1773_;
goto _start;
}
case 9:
{
lean_object* v_k_1775_; 
v_k_1775_ = lean_ctor_get(v_a_1726_, 5);
lean_inc_ref(v_k_1775_);
lean_dec_ref_known(v_a_1726_, 6);
v_a_1726_ = v_k_1775_;
goto _start;
}
case 10:
{
lean_object* v_k_1777_; 
v_k_1777_ = lean_ctor_get(v_a_1726_, 2);
lean_inc_ref(v_k_1777_);
lean_dec_ref_known(v_a_1726_, 3);
v_a_1726_ = v_k_1777_;
goto _start;
}
case 11:
{
lean_object* v_k_1779_; 
v_k_1779_ = lean_ctor_get(v_a_1726_, 2);
lean_inc_ref(v_k_1779_);
lean_dec_ref_known(v_a_1726_, 3);
v_a_1726_ = v_k_1779_;
goto _start;
}
case 12:
{
lean_object* v_k_1781_; 
v_k_1781_ = lean_ctor_get(v_a_1726_, 3);
lean_inc_ref(v_k_1781_);
lean_dec_ref_known(v_a_1726_, 4);
v_a_1726_ = v_k_1781_;
goto _start;
}
case 13:
{
lean_object* v_k_1783_; 
v_k_1783_ = lean_ctor_get(v_a_1726_, 1);
lean_inc_ref(v_k_1783_);
lean_dec_ref_known(v_a_1726_, 2);
v_a_1726_ = v_k_1783_;
goto _start;
}
default: 
{
uint8_t v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
lean_dec_ref(v_a_1726_);
lean_dec_ref(v_f_1725_);
v___x_1785_ = 0;
v___x_1786_ = lean_box(v___x_1785_);
v___x_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
return v___x_1787_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(uint8_t v_pu_1788_, lean_object* v_f_1789_, lean_object* v_as_1790_, size_t v_i_1791_, size_t v_stop_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
uint8_t v___x_1798_; 
v___x_1798_ = lean_usize_dec_eq(v_i_1791_, v_stop_1792_);
if (v___x_1798_ == 0)
{
uint8_t v___x_1799_; lean_object* v___y_1801_; lean_object* v___x_1816_; 
v___x_1799_ = 1;
v___x_1816_ = lean_array_uget_borrowed(v_as_1790_, v_i_1791_);
switch(lean_obj_tag(v___x_1816_))
{
case 0:
{
lean_object* v_code_1817_; 
v_code_1817_ = lean_ctor_get(v___x_1816_, 2);
lean_inc_ref(v_code_1817_);
v___y_1801_ = v_code_1817_;
goto v___jp_1800_;
}
case 1:
{
lean_object* v_code_1818_; 
v_code_1818_ = lean_ctor_get(v___x_1816_, 1);
lean_inc_ref(v_code_1818_);
v___y_1801_ = v_code_1818_;
goto v___jp_1800_;
}
default: 
{
lean_object* v_code_1819_; 
v_code_1819_ = lean_ctor_get(v___x_1816_, 0);
lean_inc_ref(v_code_1819_);
v___y_1801_ = v_code_1819_;
goto v___jp_1800_;
}
}
v___jp_1800_:
{
lean_object* v___x_1802_; 
lean_inc_ref(v_f_1789_);
v___x_1802_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1788_, v_f_1789_, v___y_1801_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1815_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1815_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1815_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
uint8_t v___x_1807_; 
v___x_1807_ = lean_unbox(v_a_1803_);
lean_dec(v_a_1803_);
if (v___x_1807_ == 0)
{
size_t v___x_1808_; size_t v___x_1809_; 
lean_del_object(v___x_1805_);
v___x_1808_ = ((size_t)1ULL);
v___x_1809_ = lean_usize_add(v_i_1791_, v___x_1808_);
v_i_1791_ = v___x_1809_;
goto _start;
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
lean_dec_ref(v_f_1789_);
v___x_1811_ = lean_box(v___x_1799_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1811_);
v___x_1813_ = v___x_1805_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
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
lean_dec_ref(v_f_1789_);
return v___x_1802_;
}
}
}
else
{
uint8_t v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_dec_ref(v_f_1789_);
v___x_1820_ = 0;
v___x_1821_ = lean_box(v___x_1820_);
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
return v___x_1822_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0___boxed(lean_object* v_pu_1823_, lean_object* v_f_1824_, lean_object* v_as_1825_, lean_object* v_i_1826_, lean_object* v_stop_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
uint8_t v_pu_boxed_1833_; size_t v_i_boxed_1834_; size_t v_stop_boxed_1835_; lean_object* v_res_1836_; 
v_pu_boxed_1833_ = lean_unbox(v_pu_1823_);
v_i_boxed_1834_ = lean_unbox_usize(v_i_1826_);
lean_dec(v_i_1826_);
v_stop_boxed_1835_ = lean_unbox_usize(v_stop_1827_);
lean_dec(v_stop_1827_);
v_res_1836_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(v_pu_boxed_1833_, v_f_1824_, v_as_1825_, v_i_boxed_1834_, v_stop_boxed_1835_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec_ref(v_as_1825_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go___boxed(lean_object* v_pu_1837_, lean_object* v_f_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_){
_start:
{
uint8_t v_pu_boxed_1845_; lean_object* v_res_1846_; 
v_pu_boxed_1845_ = lean_unbox(v_pu_1837_);
v_res_1846_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_boxed_1845_, v_f_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(uint8_t v_pu_1847_, lean_object* v_f_1848_, lean_object* v_as_1849_, size_t v_i_1850_, size_t v_stop_1851_, lean_object* v_b_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v_a_1859_; uint8_t v___x_1863_; 
v___x_1863_ = lean_usize_dec_eq(v_i_1850_, v_stop_1851_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; lean_object* v_value_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1864_ = lean_array_uget_borrowed(v_as_1849_, v_i_1850_);
v_value_1865_ = lean_ctor_get(v___x_1864_, 1);
v___x_1866_ = lean_box(v_pu_1847_);
lean_inc_ref(v_f_1848_);
v___x_1867_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go___boxed), 8, 2);
lean_closure_set(v___x_1867_, 0, v___x_1866_);
lean_closure_set(v___x_1867_, 1, v_f_1848_);
lean_inc_ref(v_value_1865_);
v___x_1868_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_1865_, v___x_1867_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; uint8_t v___x_1870_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref_known(v___x_1868_, 1);
v___x_1870_ = lean_unbox(v_a_1869_);
lean_dec(v_a_1869_);
if (v___x_1870_ == 0)
{
v_a_1859_ = v_b_1852_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1871_; 
lean_inc(v___x_1864_);
v___x_1871_ = lean_array_push(v_b_1852_, v___x_1864_);
v_a_1859_ = v___x_1871_;
goto v___jp_1858_;
}
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
lean_dec_ref(v_b_1852_);
lean_dec_ref(v_f_1848_);
v_a_1872_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1868_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1868_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
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
else
{
lean_object* v___x_1880_; 
lean_dec_ref(v_f_1848_);
v___x_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1880_, 0, v_b_1852_);
return v___x_1880_;
}
v___jp_1858_:
{
size_t v___x_1860_; size_t v___x_1861_; 
v___x_1860_ = ((size_t)1ULL);
v___x_1861_ = lean_usize_add(v_i_1850_, v___x_1860_);
v_i_1850_ = v___x_1861_;
v_b_1852_ = v_a_1859_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0___boxed(lean_object* v_pu_1881_, lean_object* v_f_1882_, lean_object* v_as_1883_, lean_object* v_i_1884_, lean_object* v_stop_1885_, lean_object* v_b_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
uint8_t v_pu_boxed_1892_; size_t v_i_boxed_1893_; size_t v_stop_boxed_1894_; lean_object* v_res_1895_; 
v_pu_boxed_1892_ = lean_unbox(v_pu_1881_);
v_i_boxed_1893_ = lean_unbox_usize(v_i_1884_);
lean_dec(v_i_1884_);
v_stop_boxed_1894_ = lean_unbox_usize(v_stop_1885_);
lean_dec(v_stop_1885_);
v_res_1895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_boxed_1892_, v_f_1882_, v_as_1883_, v_i_boxed_1893_, v_stop_boxed_1894_, v_b_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v_as_1883_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJp(uint8_t v_pu_1896_, lean_object* v_f_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1904_ = lean_unsigned_to_nat(0u);
v___x_1905_ = lean_array_get_size(v_a_1898_);
v___x_1906_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_1907_ = lean_nat_dec_lt(v___x_1904_, v___x_1905_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; 
lean_dec_ref(v_f_1897_);
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1906_);
return v___x_1908_;
}
else
{
size_t v___x_1909_; size_t v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = ((size_t)0ULL);
v___x_1910_ = lean_usize_of_nat(v___x_1905_);
v___x_1911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_1896_, v_f_1897_, v_a_1898_, v___x_1909_, v___x_1910_, v___x_1906_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
return v___x_1911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJp___boxed(lean_object* v_pu_1912_, lean_object* v_f_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_){
_start:
{
uint8_t v_pu_boxed_1920_; lean_object* v_res_1921_; 
v_pu_boxed_1920_ = lean_unbox(v_pu_1912_);
v_res_1921_ = l_Lean_Compiler_LCNF_Probe_filterByJp(v_pu_boxed_1920_, v_f_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec(v_a_1916_);
lean_dec_ref(v_a_1915_);
lean_dec_ref(v_a_1914_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(uint8_t v_pu_1922_, lean_object* v_f_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_){
_start:
{
switch(lean_obj_tag(v_a_1924_))
{
case 0:
{
lean_object* v_k_1930_; 
v_k_1930_ = lean_ctor_get(v_a_1924_, 1);
lean_inc_ref(v_k_1930_);
lean_dec_ref_known(v_a_1924_, 2);
v_a_1924_ = v_k_1930_;
goto _start;
}
case 1:
{
lean_object* v_decl_1932_; lean_object* v_k_1933_; lean_object* v___x_1934_; 
v_decl_1932_ = lean_ctor_get(v_a_1924_, 0);
lean_inc_ref_n(v_decl_1932_, 2);
v_k_1933_ = lean_ctor_get(v_a_1924_, 1);
lean_inc_ref(v_k_1933_);
lean_dec_ref_known(v_a_1924_, 2);
lean_inc_ref(v_f_1923_);
lean_inc(v_a_1928_);
lean_inc_ref(v_a_1927_);
lean_inc(v_a_1926_);
lean_inc_ref(v_a_1925_);
v___x_1934_ = lean_apply_6(v_f_1923_, v_decl_1932_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, lean_box(0));
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; uint8_t v___x_1936_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
v___x_1936_ = lean_unbox(v_a_1935_);
lean_dec(v_a_1935_);
if (v___x_1936_ == 0)
{
lean_object* v_value_1937_; lean_object* v___x_1938_; 
lean_dec_ref_known(v___x_1934_, 1);
v_value_1937_ = lean_ctor_get(v_decl_1932_, 4);
lean_inc_ref(v_value_1937_);
lean_dec_ref(v_decl_1932_);
lean_inc_ref(v_f_1923_);
v___x_1938_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_1922_, v_f_1923_, v_value_1937_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; uint8_t v___x_1940_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v___x_1940_ = lean_unbox(v_a_1939_);
if (v___x_1940_ == 0)
{
lean_dec_ref_known(v___x_1938_, 1);
v_a_1924_ = v_k_1933_;
goto _start;
}
else
{
lean_dec_ref(v_k_1933_);
lean_dec_ref(v_f_1923_);
return v___x_1938_;
}
}
else
{
lean_dec_ref(v_k_1933_);
lean_dec_ref(v_f_1923_);
return v___x_1938_;
}
}
else
{
lean_dec_ref(v_k_1933_);
lean_dec_ref(v_decl_1932_);
lean_dec_ref(v_f_1923_);
return v___x_1934_;
}
}
else
{
lean_dec_ref(v_k_1933_);
lean_dec_ref(v_decl_1932_);
lean_dec_ref(v_f_1923_);
return v___x_1934_;
}
}
case 2:
{
lean_object* v_decl_1942_; lean_object* v_k_1943_; lean_object* v___x_1944_; 
v_decl_1942_ = lean_ctor_get(v_a_1924_, 0);
lean_inc_ref_n(v_decl_1942_, 2);
v_k_1943_ = lean_ctor_get(v_a_1924_, 1);
lean_inc_ref(v_k_1943_);
lean_dec_ref_known(v_a_1924_, 2);
lean_inc_ref(v_f_1923_);
lean_inc(v_a_1928_);
lean_inc_ref(v_a_1927_);
lean_inc(v_a_1926_);
lean_inc_ref(v_a_1925_);
v___x_1944_ = lean_apply_6(v_f_1923_, v_decl_1942_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, lean_box(0));
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; uint8_t v___x_1946_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
v___x_1946_ = lean_unbox(v_a_1945_);
lean_dec(v_a_1945_);
if (v___x_1946_ == 0)
{
lean_object* v_value_1947_; lean_object* v___x_1948_; 
lean_dec_ref_known(v___x_1944_, 1);
v_value_1947_ = lean_ctor_get(v_decl_1942_, 4);
lean_inc_ref(v_value_1947_);
lean_dec_ref(v_decl_1942_);
lean_inc_ref(v_f_1923_);
v___x_1948_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_1922_, v_f_1923_, v_value_1947_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; uint8_t v___x_1950_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
v___x_1950_ = lean_unbox(v_a_1949_);
if (v___x_1950_ == 0)
{
lean_dec_ref_known(v___x_1948_, 1);
v_a_1924_ = v_k_1943_;
goto _start;
}
else
{
lean_dec_ref(v_k_1943_);
lean_dec_ref(v_f_1923_);
return v___x_1948_;
}
}
else
{
lean_dec_ref(v_k_1943_);
lean_dec_ref(v_f_1923_);
return v___x_1948_;
}
}
else
{
lean_dec_ref(v_k_1943_);
lean_dec_ref(v_decl_1942_);
lean_dec_ref(v_f_1923_);
return v___x_1944_;
}
}
else
{
lean_dec_ref(v_k_1943_);
lean_dec_ref(v_decl_1942_);
lean_dec_ref(v_f_1923_);
return v___x_1944_;
}
}
case 4:
{
lean_object* v_cases_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1971_; 
v_cases_1952_ = lean_ctor_get(v_a_1924_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_a_1924_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1954_ = v_a_1924_;
v_isShared_1955_ = v_isSharedCheck_1971_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_cases_1952_);
lean_dec(v_a_1924_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1971_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v_alts_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v_alts_1956_ = lean_ctor_get(v_cases_1952_, 3);
lean_inc_ref(v_alts_1956_);
lean_dec_ref(v_cases_1952_);
v___x_1957_ = lean_unsigned_to_nat(0u);
v___x_1958_ = lean_array_get_size(v_alts_1956_);
v___x_1959_ = lean_nat_dec_lt(v___x_1957_, v___x_1958_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; lean_object* v___x_1962_; 
lean_dec_ref(v_alts_1956_);
lean_dec_ref(v_f_1923_);
v___x_1960_ = lean_box(v___x_1959_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set_tag(v___x_1954_, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1960_);
v___x_1962_ = v___x_1954_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
else
{
if (v___x_1959_ == 0)
{
lean_object* v___x_1964_; lean_object* v___x_1966_; 
lean_dec_ref(v_alts_1956_);
lean_dec_ref(v_f_1923_);
v___x_1964_ = lean_box(v___x_1959_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set_tag(v___x_1954_, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1964_);
v___x_1966_ = v___x_1954_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1964_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
else
{
size_t v___x_1968_; size_t v___x_1969_; lean_object* v___x_1970_; 
lean_del_object(v___x_1954_);
v___x_1968_ = ((size_t)0ULL);
v___x_1969_ = lean_usize_of_nat(v___x_1958_);
v___x_1970_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(v_pu_1922_, v_f_1923_, v_alts_1956_, v___x_1968_, v___x_1969_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
lean_dec_ref(v_alts_1956_);
return v___x_1970_;
}
}
}
}
case 7:
{
lean_object* v_k_1972_; 
v_k_1972_ = lean_ctor_get(v_a_1924_, 3);
lean_inc_ref(v_k_1972_);
lean_dec_ref_known(v_a_1924_, 4);
v_a_1924_ = v_k_1972_;
goto _start;
}
case 8:
{
lean_object* v_k_1974_; 
v_k_1974_ = lean_ctor_get(v_a_1924_, 3);
lean_inc_ref(v_k_1974_);
lean_dec_ref_known(v_a_1924_, 4);
v_a_1924_ = v_k_1974_;
goto _start;
}
case 9:
{
lean_object* v_k_1976_; 
v_k_1976_ = lean_ctor_get(v_a_1924_, 5);
lean_inc_ref(v_k_1976_);
lean_dec_ref_known(v_a_1924_, 6);
v_a_1924_ = v_k_1976_;
goto _start;
}
case 10:
{
lean_object* v_k_1978_; 
v_k_1978_ = lean_ctor_get(v_a_1924_, 2);
lean_inc_ref(v_k_1978_);
lean_dec_ref_known(v_a_1924_, 3);
v_a_1924_ = v_k_1978_;
goto _start;
}
case 11:
{
lean_object* v_k_1980_; 
v_k_1980_ = lean_ctor_get(v_a_1924_, 2);
lean_inc_ref(v_k_1980_);
lean_dec_ref_known(v_a_1924_, 3);
v_a_1924_ = v_k_1980_;
goto _start;
}
case 12:
{
lean_object* v_k_1982_; 
v_k_1982_ = lean_ctor_get(v_a_1924_, 3);
lean_inc_ref(v_k_1982_);
lean_dec_ref_known(v_a_1924_, 4);
v_a_1924_ = v_k_1982_;
goto _start;
}
case 13:
{
lean_object* v_k_1984_; 
v_k_1984_ = lean_ctor_get(v_a_1924_, 1);
lean_inc_ref(v_k_1984_);
lean_dec_ref_known(v_a_1924_, 2);
v_a_1924_ = v_k_1984_;
goto _start;
}
default: 
{
uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
lean_dec_ref(v_a_1924_);
lean_dec_ref(v_f_1923_);
v___x_1986_ = 0;
v___x_1987_ = lean_box(v___x_1986_);
v___x_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
return v___x_1988_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(uint8_t v_pu_1989_, lean_object* v_f_1990_, lean_object* v_as_1991_, size_t v_i_1992_, size_t v_stop_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
uint8_t v___x_1999_; 
v___x_1999_ = lean_usize_dec_eq(v_i_1992_, v_stop_1993_);
if (v___x_1999_ == 0)
{
uint8_t v___x_2000_; lean_object* v___y_2002_; lean_object* v___x_2017_; 
v___x_2000_ = 1;
v___x_2017_ = lean_array_uget_borrowed(v_as_1991_, v_i_1992_);
switch(lean_obj_tag(v___x_2017_))
{
case 0:
{
lean_object* v_code_2018_; 
v_code_2018_ = lean_ctor_get(v___x_2017_, 2);
lean_inc_ref(v_code_2018_);
v___y_2002_ = v_code_2018_;
goto v___jp_2001_;
}
case 1:
{
lean_object* v_code_2019_; 
v_code_2019_ = lean_ctor_get(v___x_2017_, 1);
lean_inc_ref(v_code_2019_);
v___y_2002_ = v_code_2019_;
goto v___jp_2001_;
}
default: 
{
lean_object* v_code_2020_; 
v_code_2020_ = lean_ctor_get(v___x_2017_, 0);
lean_inc_ref(v_code_2020_);
v___y_2002_ = v_code_2020_;
goto v___jp_2001_;
}
}
v___jp_2001_:
{
lean_object* v___x_2003_; 
lean_inc_ref(v_f_1990_);
v___x_2003_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_1989_, v_f_1990_, v___y_2002_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2016_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2006_ = v___x_2003_;
v_isShared_2007_ = v_isSharedCheck_2016_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_2003_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2016_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
uint8_t v___x_2008_; 
v___x_2008_ = lean_unbox(v_a_2004_);
lean_dec(v_a_2004_);
if (v___x_2008_ == 0)
{
size_t v___x_2009_; size_t v___x_2010_; 
lean_del_object(v___x_2006_);
v___x_2009_ = ((size_t)1ULL);
v___x_2010_ = lean_usize_add(v_i_1992_, v___x_2009_);
v_i_1992_ = v___x_2010_;
goto _start;
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2014_; 
lean_dec_ref(v_f_1990_);
v___x_2012_ = lean_box(v___x_2000_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v___x_2012_);
v___x_2014_ = v___x_2006_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2012_);
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
else
{
lean_dec_ref(v_f_1990_);
return v___x_2003_;
}
}
}
else
{
uint8_t v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec_ref(v_f_1990_);
v___x_2021_ = 0;
v___x_2022_ = lean_box(v___x_2021_);
v___x_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
return v___x_2023_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0___boxed(lean_object* v_pu_2024_, lean_object* v_f_2025_, lean_object* v_as_2026_, lean_object* v_i_2027_, lean_object* v_stop_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
uint8_t v_pu_boxed_2034_; size_t v_i_boxed_2035_; size_t v_stop_boxed_2036_; lean_object* v_res_2037_; 
v_pu_boxed_2034_ = lean_unbox(v_pu_2024_);
v_i_boxed_2035_ = lean_unbox_usize(v_i_2027_);
lean_dec(v_i_2027_);
v_stop_boxed_2036_ = lean_unbox_usize(v_stop_2028_);
lean_dec(v_stop_2028_);
v_res_2037_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(v_pu_boxed_2034_, v_f_2025_, v_as_2026_, v_i_boxed_2035_, v_stop_boxed_2036_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec_ref(v_as_2026_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go___boxed(lean_object* v_pu_2038_, lean_object* v_f_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_){
_start:
{
uint8_t v_pu_boxed_2046_; lean_object* v_res_2047_; 
v_pu_boxed_2046_ = lean_unbox(v_pu_2038_);
v_res_2047_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_boxed_2046_, v_f_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
lean_dec(v_a_2044_);
lean_dec_ref(v_a_2043_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(uint8_t v_pu_2048_, lean_object* v_f_2049_, lean_object* v_as_2050_, size_t v_i_2051_, size_t v_stop_2052_, lean_object* v_b_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v_a_2060_; uint8_t v___x_2064_; 
v___x_2064_ = lean_usize_dec_eq(v_i_2051_, v_stop_2052_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; lean_object* v_value_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2065_ = lean_array_uget_borrowed(v_as_2050_, v_i_2051_);
v_value_2066_ = lean_ctor_get(v___x_2065_, 1);
v___x_2067_ = lean_box(v_pu_2048_);
lean_inc_ref(v_f_2049_);
v___x_2068_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go___boxed), 8, 2);
lean_closure_set(v___x_2068_, 0, v___x_2067_);
lean_closure_set(v___x_2068_, 1, v_f_2049_);
lean_inc_ref(v_value_2066_);
v___x_2069_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2066_, v___x_2068_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; uint8_t v___x_2071_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref_known(v___x_2069_, 1);
v___x_2071_ = lean_unbox(v_a_2070_);
lean_dec(v_a_2070_);
if (v___x_2071_ == 0)
{
v_a_2060_ = v_b_2053_;
goto v___jp_2059_;
}
else
{
lean_object* v___x_2072_; 
lean_inc(v___x_2065_);
v___x_2072_ = lean_array_push(v_b_2053_, v___x_2065_);
v_a_2060_ = v___x_2072_;
goto v___jp_2059_;
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec_ref(v_b_2053_);
lean_dec_ref(v_f_2049_);
v_a_2073_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2069_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2069_);
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
else
{
lean_object* v___x_2081_; 
lean_dec_ref(v_f_2049_);
v___x_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2081_, 0, v_b_2053_);
return v___x_2081_;
}
v___jp_2059_:
{
size_t v___x_2061_; size_t v___x_2062_; 
v___x_2061_ = ((size_t)1ULL);
v___x_2062_ = lean_usize_add(v_i_2051_, v___x_2061_);
v_i_2051_ = v___x_2062_;
v_b_2053_ = v_a_2060_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0___boxed(lean_object* v_pu_2082_, lean_object* v_f_2083_, lean_object* v_as_2084_, lean_object* v_i_2085_, lean_object* v_stop_2086_, lean_object* v_b_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
uint8_t v_pu_boxed_2093_; size_t v_i_boxed_2094_; size_t v_stop_boxed_2095_; lean_object* v_res_2096_; 
v_pu_boxed_2093_ = lean_unbox(v_pu_2082_);
v_i_boxed_2094_ = lean_unbox_usize(v_i_2085_);
lean_dec(v_i_2085_);
v_stop_boxed_2095_ = lean_unbox_usize(v_stop_2086_);
lean_dec(v_stop_2086_);
v_res_2096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_boxed_2093_, v_f_2083_, v_as_2084_, v_i_boxed_2094_, v_stop_boxed_2095_, v_b_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec_ref(v_as_2084_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFunDecl(uint8_t v_pu_2097_, lean_object* v_f_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; 
v___x_2105_ = lean_unsigned_to_nat(0u);
v___x_2106_ = lean_array_get_size(v_a_2099_);
v___x_2107_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2108_ = lean_nat_dec_lt(v___x_2105_, v___x_2106_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; 
lean_dec_ref(v_f_2098_);
v___x_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2107_);
return v___x_2109_;
}
else
{
size_t v___x_2110_; size_t v___x_2111_; lean_object* v___x_2112_; 
v___x_2110_ = ((size_t)0ULL);
v___x_2111_ = lean_usize_of_nat(v___x_2106_);
v___x_2112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_2097_, v_f_2098_, v_a_2099_, v___x_2110_, v___x_2111_, v___x_2107_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
return v___x_2112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFunDecl___boxed(lean_object* v_pu_2113_, lean_object* v_f_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
uint8_t v_pu_boxed_2121_; lean_object* v_res_2122_; 
v_pu_boxed_2121_ = lean_unbox(v_pu_2113_);
v_res_2122_ = l_Lean_Compiler_LCNF_Probe_filterByFunDecl(v_pu_boxed_2121_, v_f_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec_ref(v_a_2115_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(uint8_t v_pu_2123_, lean_object* v_f_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
switch(lean_obj_tag(v_a_2125_))
{
case 0:
{
lean_object* v_k_2131_; 
v_k_2131_ = lean_ctor_get(v_a_2125_, 1);
lean_inc_ref(v_k_2131_);
lean_dec_ref_known(v_a_2125_, 2);
v_a_2125_ = v_k_2131_;
goto _start;
}
case 1:
{
lean_object* v_decl_2133_; lean_object* v_k_2134_; lean_object* v_value_2135_; lean_object* v___x_2136_; 
v_decl_2133_ = lean_ctor_get(v_a_2125_, 0);
lean_inc_ref(v_decl_2133_);
v_k_2134_ = lean_ctor_get(v_a_2125_, 1);
lean_inc_ref(v_k_2134_);
lean_dec_ref_known(v_a_2125_, 2);
v_value_2135_ = lean_ctor_get(v_decl_2133_, 4);
lean_inc_ref(v_value_2135_);
lean_dec_ref(v_decl_2133_);
lean_inc_ref(v_f_2124_);
v___x_2136_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2123_, v_f_2124_, v_value_2135_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; uint8_t v___x_2138_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
v___x_2138_ = lean_unbox(v_a_2137_);
if (v___x_2138_ == 0)
{
lean_dec_ref_known(v___x_2136_, 1);
v_a_2125_ = v_k_2134_;
goto _start;
}
else
{
lean_dec_ref(v_k_2134_);
lean_dec_ref(v_f_2124_);
return v___x_2136_;
}
}
else
{
lean_dec_ref(v_k_2134_);
lean_dec_ref(v_f_2124_);
return v___x_2136_;
}
}
case 2:
{
lean_object* v_decl_2140_; lean_object* v_k_2141_; lean_object* v_value_2142_; lean_object* v___x_2143_; 
v_decl_2140_ = lean_ctor_get(v_a_2125_, 0);
lean_inc_ref(v_decl_2140_);
v_k_2141_ = lean_ctor_get(v_a_2125_, 1);
lean_inc_ref(v_k_2141_);
lean_dec_ref_known(v_a_2125_, 2);
v_value_2142_ = lean_ctor_get(v_decl_2140_, 4);
lean_inc_ref(v_value_2142_);
lean_dec_ref(v_decl_2140_);
lean_inc_ref(v_f_2124_);
v___x_2143_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2123_, v_f_2124_, v_value_2142_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; uint8_t v___x_2145_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
v___x_2145_ = lean_unbox(v_a_2144_);
if (v___x_2145_ == 0)
{
lean_dec_ref_known(v___x_2143_, 1);
v_a_2125_ = v_k_2141_;
goto _start;
}
else
{
lean_dec_ref(v_k_2141_);
lean_dec_ref(v_f_2124_);
return v___x_2143_;
}
}
else
{
lean_dec_ref(v_k_2141_);
lean_dec_ref(v_f_2124_);
return v___x_2143_;
}
}
case 4:
{
lean_object* v_cases_2147_; lean_object* v___x_2148_; 
v_cases_2147_ = lean_ctor_get(v_a_2125_, 0);
lean_inc_ref_n(v_cases_2147_, 2);
lean_dec_ref_known(v_a_2125_, 1);
lean_inc_ref(v_f_2124_);
lean_inc(v_a_2129_);
lean_inc_ref(v_a_2128_);
lean_inc(v_a_2127_);
lean_inc_ref(v_a_2126_);
v___x_2148_ = lean_apply_6(v_f_2124_, v_cases_2147_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, lean_box(0));
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; uint8_t v___x_2150_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
v___x_2150_ = lean_unbox(v_a_2149_);
lean_dec(v_a_2149_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2169_; 
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2169_ == 0)
{
lean_object* v_unused_2170_; 
v_unused_2170_ = lean_ctor_get(v___x_2148_, 0);
lean_dec(v_unused_2170_);
v___x_2152_ = v___x_2148_;
v_isShared_2153_ = v_isSharedCheck_2169_;
goto v_resetjp_2151_;
}
else
{
lean_dec(v___x_2148_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2169_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v_alts_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; 
v_alts_2154_ = lean_ctor_get(v_cases_2147_, 3);
lean_inc_ref(v_alts_2154_);
lean_dec_ref(v_cases_2147_);
v___x_2155_ = lean_unsigned_to_nat(0u);
v___x_2156_ = lean_array_get_size(v_alts_2154_);
v___x_2157_ = lean_nat_dec_lt(v___x_2155_, v___x_2156_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2160_; 
lean_dec_ref(v_alts_2154_);
lean_dec_ref(v_f_2124_);
v___x_2158_ = lean_box(v___x_2157_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2158_);
v___x_2160_ = v___x_2152_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
else
{
if (v___x_2157_ == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2164_; 
lean_dec_ref(v_alts_2154_);
lean_dec_ref(v_f_2124_);
v___x_2162_ = lean_box(v___x_2157_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2162_);
v___x_2164_ = v___x_2152_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
else
{
size_t v___x_2166_; size_t v___x_2167_; lean_object* v___x_2168_; 
lean_del_object(v___x_2152_);
v___x_2166_ = ((size_t)0ULL);
v___x_2167_ = lean_usize_of_nat(v___x_2156_);
v___x_2168_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(v_pu_2123_, v_f_2124_, v_alts_2154_, v___x_2166_, v___x_2167_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
lean_dec_ref(v_alts_2154_);
return v___x_2168_;
}
}
}
}
else
{
lean_dec_ref(v_cases_2147_);
lean_dec_ref(v_f_2124_);
return v___x_2148_;
}
}
else
{
lean_dec_ref(v_cases_2147_);
lean_dec_ref(v_f_2124_);
return v___x_2148_;
}
}
case 7:
{
lean_object* v_k_2171_; 
v_k_2171_ = lean_ctor_get(v_a_2125_, 3);
lean_inc_ref(v_k_2171_);
lean_dec_ref_known(v_a_2125_, 4);
v_a_2125_ = v_k_2171_;
goto _start;
}
case 8:
{
lean_object* v_k_2173_; 
v_k_2173_ = lean_ctor_get(v_a_2125_, 3);
lean_inc_ref(v_k_2173_);
lean_dec_ref_known(v_a_2125_, 4);
v_a_2125_ = v_k_2173_;
goto _start;
}
case 9:
{
lean_object* v_k_2175_; 
v_k_2175_ = lean_ctor_get(v_a_2125_, 5);
lean_inc_ref(v_k_2175_);
lean_dec_ref_known(v_a_2125_, 6);
v_a_2125_ = v_k_2175_;
goto _start;
}
case 10:
{
lean_object* v_k_2177_; 
v_k_2177_ = lean_ctor_get(v_a_2125_, 2);
lean_inc_ref(v_k_2177_);
lean_dec_ref_known(v_a_2125_, 3);
v_a_2125_ = v_k_2177_;
goto _start;
}
case 11:
{
lean_object* v_k_2179_; 
v_k_2179_ = lean_ctor_get(v_a_2125_, 2);
lean_inc_ref(v_k_2179_);
lean_dec_ref_known(v_a_2125_, 3);
v_a_2125_ = v_k_2179_;
goto _start;
}
case 12:
{
lean_object* v_k_2181_; 
v_k_2181_ = lean_ctor_get(v_a_2125_, 3);
lean_inc_ref(v_k_2181_);
lean_dec_ref_known(v_a_2125_, 4);
v_a_2125_ = v_k_2181_;
goto _start;
}
case 13:
{
lean_object* v_k_2183_; 
v_k_2183_ = lean_ctor_get(v_a_2125_, 1);
lean_inc_ref(v_k_2183_);
lean_dec_ref_known(v_a_2125_, 2);
v_a_2125_ = v_k_2183_;
goto _start;
}
default: 
{
uint8_t v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
lean_dec_ref(v_a_2125_);
lean_dec_ref(v_f_2124_);
v___x_2185_ = 0;
v___x_2186_ = lean_box(v___x_2185_);
v___x_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
return v___x_2187_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(uint8_t v_pu_2188_, lean_object* v_f_2189_, lean_object* v_as_2190_, size_t v_i_2191_, size_t v_stop_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
uint8_t v___x_2198_; 
v___x_2198_ = lean_usize_dec_eq(v_i_2191_, v_stop_2192_);
if (v___x_2198_ == 0)
{
uint8_t v___x_2199_; lean_object* v___y_2201_; lean_object* v___x_2216_; 
v___x_2199_ = 1;
v___x_2216_ = lean_array_uget_borrowed(v_as_2190_, v_i_2191_);
switch(lean_obj_tag(v___x_2216_))
{
case 0:
{
lean_object* v_code_2217_; 
v_code_2217_ = lean_ctor_get(v___x_2216_, 2);
lean_inc_ref(v_code_2217_);
v___y_2201_ = v_code_2217_;
goto v___jp_2200_;
}
case 1:
{
lean_object* v_code_2218_; 
v_code_2218_ = lean_ctor_get(v___x_2216_, 1);
lean_inc_ref(v_code_2218_);
v___y_2201_ = v_code_2218_;
goto v___jp_2200_;
}
default: 
{
lean_object* v_code_2219_; 
v_code_2219_ = lean_ctor_get(v___x_2216_, 0);
lean_inc_ref(v_code_2219_);
v___y_2201_ = v_code_2219_;
goto v___jp_2200_;
}
}
v___jp_2200_:
{
lean_object* v___x_2202_; 
lean_inc_ref(v_f_2189_);
v___x_2202_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2188_, v_f_2189_, v___y_2201_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2215_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2215_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2215_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
uint8_t v___x_2207_; 
v___x_2207_ = lean_unbox(v_a_2203_);
lean_dec(v_a_2203_);
if (v___x_2207_ == 0)
{
size_t v___x_2208_; size_t v___x_2209_; 
lean_del_object(v___x_2205_);
v___x_2208_ = ((size_t)1ULL);
v___x_2209_ = lean_usize_add(v_i_2191_, v___x_2208_);
v_i_2191_ = v___x_2209_;
goto _start;
}
else
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
lean_dec_ref(v_f_2189_);
v___x_2211_ = lean_box(v___x_2199_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2211_);
v___x_2213_ = v___x_2205_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
else
{
lean_dec_ref(v_f_2189_);
return v___x_2202_;
}
}
}
else
{
uint8_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
lean_dec_ref(v_f_2189_);
v___x_2220_ = 0;
v___x_2221_ = lean_box(v___x_2220_);
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
return v___x_2222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0___boxed(lean_object* v_pu_2223_, lean_object* v_f_2224_, lean_object* v_as_2225_, lean_object* v_i_2226_, lean_object* v_stop_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
uint8_t v_pu_boxed_2233_; size_t v_i_boxed_2234_; size_t v_stop_boxed_2235_; lean_object* v_res_2236_; 
v_pu_boxed_2233_ = lean_unbox(v_pu_2223_);
v_i_boxed_2234_ = lean_unbox_usize(v_i_2226_);
lean_dec(v_i_2226_);
v_stop_boxed_2235_ = lean_unbox_usize(v_stop_2227_);
lean_dec(v_stop_2227_);
v_res_2236_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(v_pu_boxed_2233_, v_f_2224_, v_as_2225_, v_i_boxed_2234_, v_stop_boxed_2235_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v_as_2225_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go___boxed(lean_object* v_pu_2237_, lean_object* v_f_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
uint8_t v_pu_boxed_2245_; lean_object* v_res_2246_; 
v_pu_boxed_2245_ = lean_unbox(v_pu_2237_);
v_res_2246_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_boxed_2245_, v_f_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_);
lean_dec(v_a_2243_);
lean_dec_ref(v_a_2242_);
lean_dec(v_a_2241_);
lean_dec_ref(v_a_2240_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(uint8_t v_pu_2247_, lean_object* v_f_2248_, lean_object* v_as_2249_, size_t v_i_2250_, size_t v_stop_2251_, lean_object* v_b_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v_a_2259_; uint8_t v___x_2263_; 
v___x_2263_ = lean_usize_dec_eq(v_i_2250_, v_stop_2251_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; lean_object* v_value_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2264_ = lean_array_uget_borrowed(v_as_2249_, v_i_2250_);
v_value_2265_ = lean_ctor_get(v___x_2264_, 1);
v___x_2266_ = lean_box(v_pu_2247_);
lean_inc_ref(v_f_2248_);
v___x_2267_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go___boxed), 8, 2);
lean_closure_set(v___x_2267_, 0, v___x_2266_);
lean_closure_set(v___x_2267_, 1, v_f_2248_);
lean_inc_ref(v_value_2265_);
v___x_2268_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2265_, v___x_2267_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; uint8_t v___x_2270_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v___x_2268_, 1);
v___x_2270_ = lean_unbox(v_a_2269_);
lean_dec(v_a_2269_);
if (v___x_2270_ == 0)
{
v_a_2259_ = v_b_2252_;
goto v___jp_2258_;
}
else
{
lean_object* v___x_2271_; 
lean_inc(v___x_2264_);
v___x_2271_ = lean_array_push(v_b_2252_, v___x_2264_);
v_a_2259_ = v___x_2271_;
goto v___jp_2258_;
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec_ref(v_b_2252_);
lean_dec_ref(v_f_2248_);
v_a_2272_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2268_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2268_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
else
{
lean_object* v___x_2280_; 
lean_dec_ref(v_f_2248_);
v___x_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2280_, 0, v_b_2252_);
return v___x_2280_;
}
v___jp_2258_:
{
size_t v___x_2260_; size_t v___x_2261_; 
v___x_2260_ = ((size_t)1ULL);
v___x_2261_ = lean_usize_add(v_i_2250_, v___x_2260_);
v_i_2250_ = v___x_2261_;
v_b_2252_ = v_a_2259_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0___boxed(lean_object* v_pu_2281_, lean_object* v_f_2282_, lean_object* v_as_2283_, lean_object* v_i_2284_, lean_object* v_stop_2285_, lean_object* v_b_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
uint8_t v_pu_boxed_2292_; size_t v_i_boxed_2293_; size_t v_stop_boxed_2294_; lean_object* v_res_2295_; 
v_pu_boxed_2292_ = lean_unbox(v_pu_2281_);
v_i_boxed_2293_ = lean_unbox_usize(v_i_2284_);
lean_dec(v_i_2284_);
v_stop_boxed_2294_ = lean_unbox_usize(v_stop_2285_);
lean_dec(v_stop_2285_);
v_res_2295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_boxed_2292_, v_f_2282_, v_as_2283_, v_i_boxed_2293_, v_stop_boxed_2294_, v_b_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec_ref(v_as_2283_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByCases(uint8_t v_pu_2296_, lean_object* v_f_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; uint8_t v___x_2307_; 
v___x_2304_ = lean_unsigned_to_nat(0u);
v___x_2305_ = lean_array_get_size(v_a_2298_);
v___x_2306_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2307_ = lean_nat_dec_lt(v___x_2304_, v___x_2305_);
if (v___x_2307_ == 0)
{
lean_object* v___x_2308_; 
lean_dec_ref(v_f_2297_);
v___x_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2306_);
return v___x_2308_;
}
else
{
size_t v___x_2309_; size_t v___x_2310_; lean_object* v___x_2311_; 
v___x_2309_ = ((size_t)0ULL);
v___x_2310_ = lean_usize_of_nat(v___x_2305_);
v___x_2311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_2296_, v_f_2297_, v_a_2298_, v___x_2309_, v___x_2310_, v___x_2306_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_2311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByCases___boxed(lean_object* v_pu_2312_, lean_object* v_f_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
uint8_t v_pu_boxed_2320_; lean_object* v_res_2321_; 
v_pu_boxed_2320_ = lean_unbox(v_pu_2312_);
v_res_2321_ = l_Lean_Compiler_LCNF_Probe_filterByCases(v_pu_boxed_2320_, v_f_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec_ref(v_a_2314_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(uint8_t v_pu_2322_, lean_object* v_f_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
switch(lean_obj_tag(v_a_2324_))
{
case 0:
{
lean_object* v_k_2330_; 
v_k_2330_ = lean_ctor_get(v_a_2324_, 1);
lean_inc_ref(v_k_2330_);
lean_dec_ref_known(v_a_2324_, 2);
v_a_2324_ = v_k_2330_;
goto _start;
}
case 1:
{
lean_object* v_decl_2332_; lean_object* v_k_2333_; lean_object* v_value_2334_; lean_object* v___x_2335_; 
v_decl_2332_ = lean_ctor_get(v_a_2324_, 0);
lean_inc_ref(v_decl_2332_);
v_k_2333_ = lean_ctor_get(v_a_2324_, 1);
lean_inc_ref(v_k_2333_);
lean_dec_ref_known(v_a_2324_, 2);
v_value_2334_ = lean_ctor_get(v_decl_2332_, 4);
lean_inc_ref(v_value_2334_);
lean_dec_ref(v_decl_2332_);
lean_inc_ref(v_f_2323_);
v___x_2335_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2322_, v_f_2323_, v_value_2334_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; uint8_t v___x_2337_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
v___x_2337_ = lean_unbox(v_a_2336_);
if (v___x_2337_ == 0)
{
lean_dec_ref_known(v___x_2335_, 1);
v_a_2324_ = v_k_2333_;
goto _start;
}
else
{
lean_dec_ref(v_k_2333_);
lean_dec_ref(v_f_2323_);
return v___x_2335_;
}
}
else
{
lean_dec_ref(v_k_2333_);
lean_dec_ref(v_f_2323_);
return v___x_2335_;
}
}
case 2:
{
lean_object* v_decl_2339_; lean_object* v_k_2340_; lean_object* v_value_2341_; lean_object* v___x_2342_; 
v_decl_2339_ = lean_ctor_get(v_a_2324_, 0);
lean_inc_ref(v_decl_2339_);
v_k_2340_ = lean_ctor_get(v_a_2324_, 1);
lean_inc_ref(v_k_2340_);
lean_dec_ref_known(v_a_2324_, 2);
v_value_2341_ = lean_ctor_get(v_decl_2339_, 4);
lean_inc_ref(v_value_2341_);
lean_dec_ref(v_decl_2339_);
lean_inc_ref(v_f_2323_);
v___x_2342_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2322_, v_f_2323_, v_value_2341_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; uint8_t v___x_2344_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v___x_2344_ = lean_unbox(v_a_2343_);
if (v___x_2344_ == 0)
{
lean_dec_ref_known(v___x_2342_, 1);
v_a_2324_ = v_k_2340_;
goto _start;
}
else
{
lean_dec_ref(v_k_2340_);
lean_dec_ref(v_f_2323_);
return v___x_2342_;
}
}
else
{
lean_dec_ref(v_k_2340_);
lean_dec_ref(v_f_2323_);
return v___x_2342_;
}
}
case 3:
{
lean_object* v_fvarId_2346_; lean_object* v_args_2347_; lean_object* v___x_2348_; 
v_fvarId_2346_ = lean_ctor_get(v_a_2324_, 0);
lean_inc(v_fvarId_2346_);
v_args_2347_ = lean_ctor_get(v_a_2324_, 1);
lean_inc_ref(v_args_2347_);
lean_dec_ref_known(v_a_2324_, 2);
lean_inc(v_a_2328_);
lean_inc_ref(v_a_2327_);
lean_inc(v_a_2326_);
lean_inc_ref(v_a_2325_);
v___x_2348_ = lean_apply_7(v_f_2323_, v_fvarId_2346_, v_args_2347_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, lean_box(0));
return v___x_2348_;
}
case 4:
{
lean_object* v_cases_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2368_; 
v_cases_2349_ = lean_ctor_get(v_a_2324_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v_a_2324_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2351_ = v_a_2324_;
v_isShared_2352_ = v_isSharedCheck_2368_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_cases_2349_);
lean_dec(v_a_2324_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2368_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v_alts_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; 
v_alts_2353_ = lean_ctor_get(v_cases_2349_, 3);
lean_inc_ref(v_alts_2353_);
lean_dec_ref(v_cases_2349_);
v___x_2354_ = lean_unsigned_to_nat(0u);
v___x_2355_ = lean_array_get_size(v_alts_2353_);
v___x_2356_ = lean_nat_dec_lt(v___x_2354_, v___x_2355_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; lean_object* v___x_2359_; 
lean_dec_ref(v_alts_2353_);
lean_dec_ref(v_f_2323_);
v___x_2357_ = lean_box(v___x_2356_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set_tag(v___x_2351_, 0);
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
else
{
if (v___x_2356_ == 0)
{
lean_object* v___x_2361_; lean_object* v___x_2363_; 
lean_dec_ref(v_alts_2353_);
lean_dec_ref(v_f_2323_);
v___x_2361_ = lean_box(v___x_2356_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set_tag(v___x_2351_, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2361_);
v___x_2363_ = v___x_2351_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
else
{
size_t v___x_2365_; size_t v___x_2366_; lean_object* v___x_2367_; 
lean_del_object(v___x_2351_);
v___x_2365_ = ((size_t)0ULL);
v___x_2366_ = lean_usize_of_nat(v___x_2355_);
v___x_2367_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(v_pu_2322_, v_f_2323_, v_alts_2353_, v___x_2365_, v___x_2366_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec_ref(v_alts_2353_);
return v___x_2367_;
}
}
}
}
case 7:
{
lean_object* v_k_2369_; 
v_k_2369_ = lean_ctor_get(v_a_2324_, 3);
lean_inc_ref(v_k_2369_);
lean_dec_ref_known(v_a_2324_, 4);
v_a_2324_ = v_k_2369_;
goto _start;
}
case 8:
{
lean_object* v_k_2371_; 
v_k_2371_ = lean_ctor_get(v_a_2324_, 3);
lean_inc_ref(v_k_2371_);
lean_dec_ref_known(v_a_2324_, 4);
v_a_2324_ = v_k_2371_;
goto _start;
}
case 9:
{
lean_object* v_k_2373_; 
v_k_2373_ = lean_ctor_get(v_a_2324_, 5);
lean_inc_ref(v_k_2373_);
lean_dec_ref_known(v_a_2324_, 6);
v_a_2324_ = v_k_2373_;
goto _start;
}
case 10:
{
lean_object* v_k_2375_; 
v_k_2375_ = lean_ctor_get(v_a_2324_, 2);
lean_inc_ref(v_k_2375_);
lean_dec_ref_known(v_a_2324_, 3);
v_a_2324_ = v_k_2375_;
goto _start;
}
case 11:
{
lean_object* v_k_2377_; 
v_k_2377_ = lean_ctor_get(v_a_2324_, 2);
lean_inc_ref(v_k_2377_);
lean_dec_ref_known(v_a_2324_, 3);
v_a_2324_ = v_k_2377_;
goto _start;
}
case 12:
{
lean_object* v_k_2379_; 
v_k_2379_ = lean_ctor_get(v_a_2324_, 3);
lean_inc_ref(v_k_2379_);
lean_dec_ref_known(v_a_2324_, 4);
v_a_2324_ = v_k_2379_;
goto _start;
}
case 13:
{
lean_object* v_k_2381_; 
v_k_2381_ = lean_ctor_get(v_a_2324_, 1);
lean_inc_ref(v_k_2381_);
lean_dec_ref_known(v_a_2324_, 2);
v_a_2324_ = v_k_2381_;
goto _start;
}
default: 
{
uint8_t v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
lean_dec_ref(v_a_2324_);
lean_dec_ref(v_f_2323_);
v___x_2383_ = 0;
v___x_2384_ = lean_box(v___x_2383_);
v___x_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
return v___x_2385_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(uint8_t v_pu_2386_, lean_object* v_f_2387_, lean_object* v_as_2388_, size_t v_i_2389_, size_t v_stop_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
uint8_t v___x_2396_; 
v___x_2396_ = lean_usize_dec_eq(v_i_2389_, v_stop_2390_);
if (v___x_2396_ == 0)
{
uint8_t v___x_2397_; lean_object* v___y_2399_; lean_object* v___x_2414_; 
v___x_2397_ = 1;
v___x_2414_ = lean_array_uget_borrowed(v_as_2388_, v_i_2389_);
switch(lean_obj_tag(v___x_2414_))
{
case 0:
{
lean_object* v_code_2415_; 
v_code_2415_ = lean_ctor_get(v___x_2414_, 2);
lean_inc_ref(v_code_2415_);
v___y_2399_ = v_code_2415_;
goto v___jp_2398_;
}
case 1:
{
lean_object* v_code_2416_; 
v_code_2416_ = lean_ctor_get(v___x_2414_, 1);
lean_inc_ref(v_code_2416_);
v___y_2399_ = v_code_2416_;
goto v___jp_2398_;
}
default: 
{
lean_object* v_code_2417_; 
v_code_2417_ = lean_ctor_get(v___x_2414_, 0);
lean_inc_ref(v_code_2417_);
v___y_2399_ = v_code_2417_;
goto v___jp_2398_;
}
}
v___jp_2398_:
{
lean_object* v___x_2400_; 
lean_inc_ref(v_f_2387_);
v___x_2400_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2386_, v_f_2387_, v___y_2399_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2413_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2403_ = v___x_2400_;
v_isShared_2404_ = v_isSharedCheck_2413_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2400_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2413_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
uint8_t v___x_2405_; 
v___x_2405_ = lean_unbox(v_a_2401_);
lean_dec(v_a_2401_);
if (v___x_2405_ == 0)
{
size_t v___x_2406_; size_t v___x_2407_; 
lean_del_object(v___x_2403_);
v___x_2406_ = ((size_t)1ULL);
v___x_2407_ = lean_usize_add(v_i_2389_, v___x_2406_);
v_i_2389_ = v___x_2407_;
goto _start;
}
else
{
lean_object* v___x_2409_; lean_object* v___x_2411_; 
lean_dec_ref(v_f_2387_);
v___x_2409_ = lean_box(v___x_2397_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 0, v___x_2409_);
v___x_2411_ = v___x_2403_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
else
{
lean_dec_ref(v_f_2387_);
return v___x_2400_;
}
}
}
else
{
uint8_t v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
lean_dec_ref(v_f_2387_);
v___x_2418_ = 0;
v___x_2419_ = lean_box(v___x_2418_);
v___x_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
return v___x_2420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0___boxed(lean_object* v_pu_2421_, lean_object* v_f_2422_, lean_object* v_as_2423_, lean_object* v_i_2424_, lean_object* v_stop_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
uint8_t v_pu_boxed_2431_; size_t v_i_boxed_2432_; size_t v_stop_boxed_2433_; lean_object* v_res_2434_; 
v_pu_boxed_2431_ = lean_unbox(v_pu_2421_);
v_i_boxed_2432_ = lean_unbox_usize(v_i_2424_);
lean_dec(v_i_2424_);
v_stop_boxed_2433_ = lean_unbox_usize(v_stop_2425_);
lean_dec(v_stop_2425_);
v_res_2434_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(v_pu_boxed_2431_, v_f_2422_, v_as_2423_, v_i_boxed_2432_, v_stop_boxed_2433_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec_ref(v_as_2423_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go___boxed(lean_object* v_pu_2435_, lean_object* v_f_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_){
_start:
{
uint8_t v_pu_boxed_2443_; lean_object* v_res_2444_; 
v_pu_boxed_2443_ = lean_unbox(v_pu_2435_);
v_res_2444_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_boxed_2443_, v_f_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_);
lean_dec(v_a_2441_);
lean_dec_ref(v_a_2440_);
lean_dec(v_a_2439_);
lean_dec_ref(v_a_2438_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(uint8_t v_pu_2445_, lean_object* v_f_2446_, lean_object* v_as_2447_, size_t v_i_2448_, size_t v_stop_2449_, lean_object* v_b_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v_a_2457_; uint8_t v___x_2461_; 
v___x_2461_ = lean_usize_dec_eq(v_i_2448_, v_stop_2449_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; lean_object* v_value_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2462_ = lean_array_uget_borrowed(v_as_2447_, v_i_2448_);
v_value_2463_ = lean_ctor_get(v___x_2462_, 1);
v___x_2464_ = lean_box(v_pu_2445_);
lean_inc_ref(v_f_2446_);
v___x_2465_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go___boxed), 8, 2);
lean_closure_set(v___x_2465_, 0, v___x_2464_);
lean_closure_set(v___x_2465_, 1, v_f_2446_);
lean_inc_ref(v_value_2463_);
v___x_2466_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2463_, v___x_2465_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; uint8_t v___x_2468_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
lean_dec_ref_known(v___x_2466_, 1);
v___x_2468_ = lean_unbox(v_a_2467_);
lean_dec(v_a_2467_);
if (v___x_2468_ == 0)
{
v_a_2457_ = v_b_2450_;
goto v___jp_2456_;
}
else
{
lean_object* v___x_2469_; 
lean_inc(v___x_2462_);
v___x_2469_ = lean_array_push(v_b_2450_, v___x_2462_);
v_a_2457_ = v___x_2469_;
goto v___jp_2456_;
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_dec_ref(v_b_2450_);
lean_dec_ref(v_f_2446_);
v_a_2470_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2466_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2466_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
else
{
lean_object* v___x_2478_; 
lean_dec_ref(v_f_2446_);
v___x_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2478_, 0, v_b_2450_);
return v___x_2478_;
}
v___jp_2456_:
{
size_t v___x_2458_; size_t v___x_2459_; 
v___x_2458_ = ((size_t)1ULL);
v___x_2459_ = lean_usize_add(v_i_2448_, v___x_2458_);
v_i_2448_ = v___x_2459_;
v_b_2450_ = v_a_2457_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0___boxed(lean_object* v_pu_2479_, lean_object* v_f_2480_, lean_object* v_as_2481_, lean_object* v_i_2482_, lean_object* v_stop_2483_, lean_object* v_b_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
uint8_t v_pu_boxed_2490_; size_t v_i_boxed_2491_; size_t v_stop_boxed_2492_; lean_object* v_res_2493_; 
v_pu_boxed_2490_ = lean_unbox(v_pu_2479_);
v_i_boxed_2491_ = lean_unbox_usize(v_i_2482_);
lean_dec(v_i_2482_);
v_stop_boxed_2492_ = lean_unbox_usize(v_stop_2483_);
lean_dec(v_stop_2483_);
v_res_2493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_boxed_2490_, v_f_2480_, v_as_2481_, v_i_boxed_2491_, v_stop_boxed_2492_, v_b_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec_ref(v_as_2481_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJmp(uint8_t v_pu_2494_, lean_object* v_f_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; uint8_t v___x_2505_; 
v___x_2502_ = lean_unsigned_to_nat(0u);
v___x_2503_ = lean_array_get_size(v_a_2496_);
v___x_2504_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2505_ = lean_nat_dec_lt(v___x_2502_, v___x_2503_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; 
lean_dec_ref(v_f_2495_);
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2504_);
return v___x_2506_;
}
else
{
size_t v___x_2507_; size_t v___x_2508_; lean_object* v___x_2509_; 
v___x_2507_ = ((size_t)0ULL);
v___x_2508_ = lean_usize_of_nat(v___x_2503_);
v___x_2509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_2494_, v_f_2495_, v_a_2496_, v___x_2507_, v___x_2508_, v___x_2504_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_);
return v___x_2509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJmp___boxed(lean_object* v_pu_2510_, lean_object* v_f_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_){
_start:
{
uint8_t v_pu_boxed_2518_; lean_object* v_res_2519_; 
v_pu_boxed_2518_ = lean_unbox(v_pu_2510_);
v_res_2519_ = l_Lean_Compiler_LCNF_Probe_filterByJmp(v_pu_boxed_2518_, v_f_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
lean_dec_ref(v_a_2512_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(uint8_t v_pu_2520_, lean_object* v_f_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
switch(lean_obj_tag(v_a_2522_))
{
case 0:
{
lean_object* v_k_2528_; 
v_k_2528_ = lean_ctor_get(v_a_2522_, 1);
lean_inc_ref(v_k_2528_);
lean_dec_ref_known(v_a_2522_, 2);
v_a_2522_ = v_k_2528_;
goto _start;
}
case 1:
{
lean_object* v_decl_2530_; lean_object* v_k_2531_; lean_object* v_value_2532_; lean_object* v___x_2533_; 
v_decl_2530_ = lean_ctor_get(v_a_2522_, 0);
lean_inc_ref(v_decl_2530_);
v_k_2531_ = lean_ctor_get(v_a_2522_, 1);
lean_inc_ref(v_k_2531_);
lean_dec_ref_known(v_a_2522_, 2);
v_value_2532_ = lean_ctor_get(v_decl_2530_, 4);
lean_inc_ref(v_value_2532_);
lean_dec_ref(v_decl_2530_);
lean_inc_ref(v_f_2521_);
v___x_2533_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2520_, v_f_2521_, v_value_2532_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; uint8_t v___x_2535_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
v___x_2535_ = lean_unbox(v_a_2534_);
if (v___x_2535_ == 0)
{
lean_dec_ref_known(v___x_2533_, 1);
v_a_2522_ = v_k_2531_;
goto _start;
}
else
{
lean_dec_ref(v_k_2531_);
lean_dec_ref(v_f_2521_);
return v___x_2533_;
}
}
else
{
lean_dec_ref(v_k_2531_);
lean_dec_ref(v_f_2521_);
return v___x_2533_;
}
}
case 2:
{
lean_object* v_decl_2537_; lean_object* v_k_2538_; lean_object* v_value_2539_; lean_object* v___x_2540_; 
v_decl_2537_ = lean_ctor_get(v_a_2522_, 0);
lean_inc_ref(v_decl_2537_);
v_k_2538_ = lean_ctor_get(v_a_2522_, 1);
lean_inc_ref(v_k_2538_);
lean_dec_ref_known(v_a_2522_, 2);
v_value_2539_ = lean_ctor_get(v_decl_2537_, 4);
lean_inc_ref(v_value_2539_);
lean_dec_ref(v_decl_2537_);
lean_inc_ref(v_f_2521_);
v___x_2540_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2520_, v_f_2521_, v_value_2539_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v_a_2541_; uint8_t v___x_2542_; 
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
v___x_2542_ = lean_unbox(v_a_2541_);
if (v___x_2542_ == 0)
{
lean_dec_ref_known(v___x_2540_, 1);
v_a_2522_ = v_k_2538_;
goto _start;
}
else
{
lean_dec_ref(v_k_2538_);
lean_dec_ref(v_f_2521_);
return v___x_2540_;
}
}
else
{
lean_dec_ref(v_k_2538_);
lean_dec_ref(v_f_2521_);
return v___x_2540_;
}
}
case 4:
{
lean_object* v_cases_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2563_; 
v_cases_2544_ = lean_ctor_get(v_a_2522_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_a_2522_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2546_ = v_a_2522_;
v_isShared_2547_ = v_isSharedCheck_2563_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_cases_2544_);
lean_dec(v_a_2522_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2563_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v_alts_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; 
v_alts_2548_ = lean_ctor_get(v_cases_2544_, 3);
lean_inc_ref(v_alts_2548_);
lean_dec_ref(v_cases_2544_);
v___x_2549_ = lean_unsigned_to_nat(0u);
v___x_2550_ = lean_array_get_size(v_alts_2548_);
v___x_2551_ = lean_nat_dec_lt(v___x_2549_, v___x_2550_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; lean_object* v___x_2554_; 
lean_dec_ref(v_alts_2548_);
lean_dec_ref(v_f_2521_);
v___x_2552_ = lean_box(v___x_2551_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set_tag(v___x_2546_, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2552_);
v___x_2554_ = v___x_2546_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2552_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
else
{
if (v___x_2551_ == 0)
{
lean_object* v___x_2556_; lean_object* v___x_2558_; 
lean_dec_ref(v_alts_2548_);
lean_dec_ref(v_f_2521_);
v___x_2556_ = lean_box(v___x_2551_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set_tag(v___x_2546_, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2556_);
v___x_2558_ = v___x_2546_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2556_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
else
{
size_t v___x_2560_; size_t v___x_2561_; lean_object* v___x_2562_; 
lean_del_object(v___x_2546_);
v___x_2560_ = ((size_t)0ULL);
v___x_2561_ = lean_usize_of_nat(v___x_2550_);
v___x_2562_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(v_pu_2520_, v_f_2521_, v_alts_2548_, v___x_2560_, v___x_2561_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
lean_dec_ref(v_alts_2548_);
return v___x_2562_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_2564_; lean_object* v___x_2565_; 
v_fvarId_2564_ = lean_ctor_get(v_a_2522_, 0);
lean_inc(v_fvarId_2564_);
lean_dec_ref_known(v_a_2522_, 1);
lean_inc(v_a_2526_);
lean_inc_ref(v_a_2525_);
lean_inc(v_a_2524_);
lean_inc_ref(v_a_2523_);
v___x_2565_ = lean_apply_6(v_f_2521_, v_fvarId_2564_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, lean_box(0));
return v___x_2565_;
}
case 7:
{
lean_object* v_k_2566_; 
v_k_2566_ = lean_ctor_get(v_a_2522_, 3);
lean_inc_ref(v_k_2566_);
lean_dec_ref_known(v_a_2522_, 4);
v_a_2522_ = v_k_2566_;
goto _start;
}
case 8:
{
lean_object* v_k_2568_; 
v_k_2568_ = lean_ctor_get(v_a_2522_, 3);
lean_inc_ref(v_k_2568_);
lean_dec_ref_known(v_a_2522_, 4);
v_a_2522_ = v_k_2568_;
goto _start;
}
case 9:
{
lean_object* v_k_2570_; 
v_k_2570_ = lean_ctor_get(v_a_2522_, 5);
lean_inc_ref(v_k_2570_);
lean_dec_ref_known(v_a_2522_, 6);
v_a_2522_ = v_k_2570_;
goto _start;
}
case 10:
{
lean_object* v_k_2572_; 
v_k_2572_ = lean_ctor_get(v_a_2522_, 2);
lean_inc_ref(v_k_2572_);
lean_dec_ref_known(v_a_2522_, 3);
v_a_2522_ = v_k_2572_;
goto _start;
}
case 11:
{
lean_object* v_k_2574_; 
v_k_2574_ = lean_ctor_get(v_a_2522_, 2);
lean_inc_ref(v_k_2574_);
lean_dec_ref_known(v_a_2522_, 3);
v_a_2522_ = v_k_2574_;
goto _start;
}
case 12:
{
lean_object* v_k_2576_; 
v_k_2576_ = lean_ctor_get(v_a_2522_, 3);
lean_inc_ref(v_k_2576_);
lean_dec_ref_known(v_a_2522_, 4);
v_a_2522_ = v_k_2576_;
goto _start;
}
case 13:
{
lean_object* v_k_2578_; 
v_k_2578_ = lean_ctor_get(v_a_2522_, 1);
lean_inc_ref(v_k_2578_);
lean_dec_ref_known(v_a_2522_, 2);
v_a_2522_ = v_k_2578_;
goto _start;
}
default: 
{
uint8_t v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
lean_dec_ref(v_a_2522_);
lean_dec_ref(v_f_2521_);
v___x_2580_ = 0;
v___x_2581_ = lean_box(v___x_2580_);
v___x_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2581_);
return v___x_2582_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(uint8_t v_pu_2583_, lean_object* v_f_2584_, lean_object* v_as_2585_, size_t v_i_2586_, size_t v_stop_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
uint8_t v___x_2593_; 
v___x_2593_ = lean_usize_dec_eq(v_i_2586_, v_stop_2587_);
if (v___x_2593_ == 0)
{
uint8_t v___x_2594_; lean_object* v___y_2596_; lean_object* v___x_2611_; 
v___x_2594_ = 1;
v___x_2611_ = lean_array_uget_borrowed(v_as_2585_, v_i_2586_);
switch(lean_obj_tag(v___x_2611_))
{
case 0:
{
lean_object* v_code_2612_; 
v_code_2612_ = lean_ctor_get(v___x_2611_, 2);
lean_inc_ref(v_code_2612_);
v___y_2596_ = v_code_2612_;
goto v___jp_2595_;
}
case 1:
{
lean_object* v_code_2613_; 
v_code_2613_ = lean_ctor_get(v___x_2611_, 1);
lean_inc_ref(v_code_2613_);
v___y_2596_ = v_code_2613_;
goto v___jp_2595_;
}
default: 
{
lean_object* v_code_2614_; 
v_code_2614_ = lean_ctor_get(v___x_2611_, 0);
lean_inc_ref(v_code_2614_);
v___y_2596_ = v_code_2614_;
goto v___jp_2595_;
}
}
v___jp_2595_:
{
lean_object* v___x_2597_; 
lean_inc_ref(v_f_2584_);
v___x_2597_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2583_, v_f_2584_, v___y_2596_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2610_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2600_ = v___x_2597_;
v_isShared_2601_ = v_isSharedCheck_2610_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2597_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2610_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
uint8_t v___x_2602_; 
v___x_2602_ = lean_unbox(v_a_2598_);
lean_dec(v_a_2598_);
if (v___x_2602_ == 0)
{
size_t v___x_2603_; size_t v___x_2604_; 
lean_del_object(v___x_2600_);
v___x_2603_ = ((size_t)1ULL);
v___x_2604_ = lean_usize_add(v_i_2586_, v___x_2603_);
v_i_2586_ = v___x_2604_;
goto _start;
}
else
{
lean_object* v___x_2606_; lean_object* v___x_2608_; 
lean_dec_ref(v_f_2584_);
v___x_2606_ = lean_box(v___x_2594_);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v___x_2606_);
v___x_2608_ = v___x_2600_;
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
}
}
else
{
lean_dec_ref(v_f_2584_);
return v___x_2597_;
}
}
}
else
{
uint8_t v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
lean_dec_ref(v_f_2584_);
v___x_2615_ = 0;
v___x_2616_ = lean_box(v___x_2615_);
v___x_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
return v___x_2617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0___boxed(lean_object* v_pu_2618_, lean_object* v_f_2619_, lean_object* v_as_2620_, lean_object* v_i_2621_, lean_object* v_stop_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
uint8_t v_pu_boxed_2628_; size_t v_i_boxed_2629_; size_t v_stop_boxed_2630_; lean_object* v_res_2631_; 
v_pu_boxed_2628_ = lean_unbox(v_pu_2618_);
v_i_boxed_2629_ = lean_unbox_usize(v_i_2621_);
lean_dec(v_i_2621_);
v_stop_boxed_2630_ = lean_unbox_usize(v_stop_2622_);
lean_dec(v_stop_2622_);
v_res_2631_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(v_pu_boxed_2628_, v_f_2619_, v_as_2620_, v_i_boxed_2629_, v_stop_boxed_2630_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec_ref(v_as_2620_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go___boxed(lean_object* v_pu_2632_, lean_object* v_f_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_){
_start:
{
uint8_t v_pu_boxed_2640_; lean_object* v_res_2641_; 
v_pu_boxed_2640_ = lean_unbox(v_pu_2632_);
v_res_2641_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_boxed_2640_, v_f_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_);
lean_dec(v_a_2638_);
lean_dec_ref(v_a_2637_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(uint8_t v_pu_2642_, lean_object* v_f_2643_, lean_object* v_as_2644_, size_t v_i_2645_, size_t v_stop_2646_, lean_object* v_b_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v_a_2654_; uint8_t v___x_2658_; 
v___x_2658_ = lean_usize_dec_eq(v_i_2645_, v_stop_2646_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2659_; lean_object* v_value_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2659_ = lean_array_uget_borrowed(v_as_2644_, v_i_2645_);
v_value_2660_ = lean_ctor_get(v___x_2659_, 1);
v___x_2661_ = lean_box(v_pu_2642_);
lean_inc_ref(v_f_2643_);
v___x_2662_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go___boxed), 8, 2);
lean_closure_set(v___x_2662_, 0, v___x_2661_);
lean_closure_set(v___x_2662_, 1, v_f_2643_);
lean_inc_ref(v_value_2660_);
v___x_2663_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2660_, v___x_2662_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; uint8_t v___x_2665_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2664_);
lean_dec_ref_known(v___x_2663_, 1);
v___x_2665_ = lean_unbox(v_a_2664_);
lean_dec(v_a_2664_);
if (v___x_2665_ == 0)
{
v_a_2654_ = v_b_2647_;
goto v___jp_2653_;
}
else
{
lean_object* v___x_2666_; 
lean_inc(v___x_2659_);
v___x_2666_ = lean_array_push(v_b_2647_, v___x_2659_);
v_a_2654_ = v___x_2666_;
goto v___jp_2653_;
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_dec_ref(v_b_2647_);
lean_dec_ref(v_f_2643_);
v_a_2667_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2663_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2663_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
else
{
lean_object* v___x_2675_; 
lean_dec_ref(v_f_2643_);
v___x_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2675_, 0, v_b_2647_);
return v___x_2675_;
}
v___jp_2653_:
{
size_t v___x_2655_; size_t v___x_2656_; 
v___x_2655_ = ((size_t)1ULL);
v___x_2656_ = lean_usize_add(v_i_2645_, v___x_2655_);
v_i_2645_ = v___x_2656_;
v_b_2647_ = v_a_2654_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0___boxed(lean_object* v_pu_2676_, lean_object* v_f_2677_, lean_object* v_as_2678_, lean_object* v_i_2679_, lean_object* v_stop_2680_, lean_object* v_b_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
uint8_t v_pu_boxed_2687_; size_t v_i_boxed_2688_; size_t v_stop_boxed_2689_; lean_object* v_res_2690_; 
v_pu_boxed_2687_ = lean_unbox(v_pu_2676_);
v_i_boxed_2688_ = lean_unbox_usize(v_i_2679_);
lean_dec(v_i_2679_);
v_stop_boxed_2689_ = lean_unbox_usize(v_stop_2680_);
lean_dec(v_stop_2680_);
v_res_2690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_boxed_2687_, v_f_2677_, v_as_2678_, v_i_boxed_2688_, v_stop_boxed_2689_, v_b_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec_ref(v_as_2678_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByReturn(uint8_t v_pu_2691_, lean_object* v_f_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; uint8_t v___x_2702_; 
v___x_2699_ = lean_unsigned_to_nat(0u);
v___x_2700_ = lean_array_get_size(v_a_2693_);
v___x_2701_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2702_ = lean_nat_dec_lt(v___x_2699_, v___x_2700_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; 
lean_dec_ref(v_f_2692_);
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
return v___x_2703_;
}
else
{
size_t v___x_2704_; size_t v___x_2705_; lean_object* v___x_2706_; 
v___x_2704_ = ((size_t)0ULL);
v___x_2705_ = lean_usize_of_nat(v___x_2700_);
v___x_2706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_2691_, v_f_2692_, v_a_2693_, v___x_2704_, v___x_2705_, v___x_2701_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
return v___x_2706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByReturn___boxed(lean_object* v_pu_2707_, lean_object* v_f_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
uint8_t v_pu_boxed_2715_; lean_object* v_res_2716_; 
v_pu_boxed_2715_ = lean_unbox(v_pu_2707_);
v_res_2716_ = l_Lean_Compiler_LCNF_Probe_filterByReturn(v_pu_boxed_2715_, v_f_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
lean_dec_ref(v_a_2709_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(uint8_t v_pu_2717_, lean_object* v_f_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_){
_start:
{
switch(lean_obj_tag(v_a_2719_))
{
case 0:
{
lean_object* v_k_2725_; 
v_k_2725_ = lean_ctor_get(v_a_2719_, 1);
lean_inc_ref(v_k_2725_);
lean_dec_ref_known(v_a_2719_, 2);
v_a_2719_ = v_k_2725_;
goto _start;
}
case 1:
{
lean_object* v_decl_2727_; lean_object* v_k_2728_; lean_object* v_value_2729_; lean_object* v___x_2730_; 
v_decl_2727_ = lean_ctor_get(v_a_2719_, 0);
lean_inc_ref(v_decl_2727_);
v_k_2728_ = lean_ctor_get(v_a_2719_, 1);
lean_inc_ref(v_k_2728_);
lean_dec_ref_known(v_a_2719_, 2);
v_value_2729_ = lean_ctor_get(v_decl_2727_, 4);
lean_inc_ref(v_value_2729_);
lean_dec_ref(v_decl_2727_);
lean_inc_ref(v_f_2718_);
v___x_2730_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2717_, v_f_2718_, v_value_2729_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; uint8_t v___x_2732_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
v___x_2732_ = lean_unbox(v_a_2731_);
if (v___x_2732_ == 0)
{
lean_dec_ref_known(v___x_2730_, 1);
v_a_2719_ = v_k_2728_;
goto _start;
}
else
{
lean_dec_ref(v_k_2728_);
lean_dec_ref(v_f_2718_);
return v___x_2730_;
}
}
else
{
lean_dec_ref(v_k_2728_);
lean_dec_ref(v_f_2718_);
return v___x_2730_;
}
}
case 2:
{
lean_object* v_decl_2734_; lean_object* v_k_2735_; lean_object* v_value_2736_; lean_object* v___x_2737_; 
v_decl_2734_ = lean_ctor_get(v_a_2719_, 0);
lean_inc_ref(v_decl_2734_);
v_k_2735_ = lean_ctor_get(v_a_2719_, 1);
lean_inc_ref(v_k_2735_);
lean_dec_ref_known(v_a_2719_, 2);
v_value_2736_ = lean_ctor_get(v_decl_2734_, 4);
lean_inc_ref(v_value_2736_);
lean_dec_ref(v_decl_2734_);
lean_inc_ref(v_f_2718_);
v___x_2737_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2717_, v_f_2718_, v_value_2736_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; uint8_t v___x_2739_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
v___x_2739_ = lean_unbox(v_a_2738_);
if (v___x_2739_ == 0)
{
lean_dec_ref_known(v___x_2737_, 1);
v_a_2719_ = v_k_2735_;
goto _start;
}
else
{
lean_dec_ref(v_k_2735_);
lean_dec_ref(v_f_2718_);
return v___x_2737_;
}
}
else
{
lean_dec_ref(v_k_2735_);
lean_dec_ref(v_f_2718_);
return v___x_2737_;
}
}
case 4:
{
lean_object* v_cases_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2760_; 
v_cases_2741_ = lean_ctor_get(v_a_2719_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v_a_2719_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2743_ = v_a_2719_;
v_isShared_2744_ = v_isSharedCheck_2760_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_cases_2741_);
lean_dec(v_a_2719_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2760_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v_alts_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; uint8_t v___x_2748_; 
v_alts_2745_ = lean_ctor_get(v_cases_2741_, 3);
lean_inc_ref(v_alts_2745_);
lean_dec_ref(v_cases_2741_);
v___x_2746_ = lean_unsigned_to_nat(0u);
v___x_2747_ = lean_array_get_size(v_alts_2745_);
v___x_2748_ = lean_nat_dec_lt(v___x_2746_, v___x_2747_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2749_; lean_object* v___x_2751_; 
lean_dec_ref(v_alts_2745_);
lean_dec_ref(v_f_2718_);
v___x_2749_ = lean_box(v___x_2748_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set_tag(v___x_2743_, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2749_);
v___x_2751_ = v___x_2743_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2749_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
else
{
if (v___x_2748_ == 0)
{
lean_object* v___x_2753_; lean_object* v___x_2755_; 
lean_dec_ref(v_alts_2745_);
lean_dec_ref(v_f_2718_);
v___x_2753_ = lean_box(v___x_2748_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set_tag(v___x_2743_, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2753_);
v___x_2755_ = v___x_2743_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
else
{
size_t v___x_2757_; size_t v___x_2758_; lean_object* v___x_2759_; 
lean_del_object(v___x_2743_);
v___x_2757_ = ((size_t)0ULL);
v___x_2758_ = lean_usize_of_nat(v___x_2747_);
v___x_2759_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(v_pu_2717_, v_f_2718_, v_alts_2745_, v___x_2757_, v___x_2758_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
lean_dec_ref(v_alts_2745_);
return v___x_2759_;
}
}
}
}
case 6:
{
lean_object* v_type_2761_; lean_object* v___x_2762_; 
v_type_2761_ = lean_ctor_get(v_a_2719_, 0);
lean_inc_ref(v_type_2761_);
lean_dec_ref_known(v_a_2719_, 1);
lean_inc(v_a_2723_);
lean_inc_ref(v_a_2722_);
lean_inc(v_a_2721_);
lean_inc_ref(v_a_2720_);
v___x_2762_ = lean_apply_6(v_f_2718_, v_type_2761_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, lean_box(0));
return v___x_2762_;
}
case 7:
{
lean_object* v_k_2763_; 
v_k_2763_ = lean_ctor_get(v_a_2719_, 3);
lean_inc_ref(v_k_2763_);
lean_dec_ref_known(v_a_2719_, 4);
v_a_2719_ = v_k_2763_;
goto _start;
}
case 8:
{
lean_object* v_k_2765_; 
v_k_2765_ = lean_ctor_get(v_a_2719_, 3);
lean_inc_ref(v_k_2765_);
lean_dec_ref_known(v_a_2719_, 4);
v_a_2719_ = v_k_2765_;
goto _start;
}
case 9:
{
lean_object* v_k_2767_; 
v_k_2767_ = lean_ctor_get(v_a_2719_, 5);
lean_inc_ref(v_k_2767_);
lean_dec_ref_known(v_a_2719_, 6);
v_a_2719_ = v_k_2767_;
goto _start;
}
case 10:
{
lean_object* v_k_2769_; 
v_k_2769_ = lean_ctor_get(v_a_2719_, 2);
lean_inc_ref(v_k_2769_);
lean_dec_ref_known(v_a_2719_, 3);
v_a_2719_ = v_k_2769_;
goto _start;
}
case 11:
{
lean_object* v_k_2771_; 
v_k_2771_ = lean_ctor_get(v_a_2719_, 2);
lean_inc_ref(v_k_2771_);
lean_dec_ref_known(v_a_2719_, 3);
v_a_2719_ = v_k_2771_;
goto _start;
}
case 12:
{
lean_object* v_k_2773_; 
v_k_2773_ = lean_ctor_get(v_a_2719_, 3);
lean_inc_ref(v_k_2773_);
lean_dec_ref_known(v_a_2719_, 4);
v_a_2719_ = v_k_2773_;
goto _start;
}
case 13:
{
lean_object* v_k_2775_; 
v_k_2775_ = lean_ctor_get(v_a_2719_, 1);
lean_inc_ref(v_k_2775_);
lean_dec_ref_known(v_a_2719_, 2);
v_a_2719_ = v_k_2775_;
goto _start;
}
default: 
{
uint8_t v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
lean_dec_ref(v_a_2719_);
lean_dec_ref(v_f_2718_);
v___x_2777_ = 0;
v___x_2778_ = lean_box(v___x_2777_);
v___x_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2778_);
return v___x_2779_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(uint8_t v_pu_2780_, lean_object* v_f_2781_, lean_object* v_as_2782_, size_t v_i_2783_, size_t v_stop_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
uint8_t v___x_2790_; 
v___x_2790_ = lean_usize_dec_eq(v_i_2783_, v_stop_2784_);
if (v___x_2790_ == 0)
{
uint8_t v___x_2791_; lean_object* v___y_2793_; lean_object* v___x_2808_; 
v___x_2791_ = 1;
v___x_2808_ = lean_array_uget_borrowed(v_as_2782_, v_i_2783_);
switch(lean_obj_tag(v___x_2808_))
{
case 0:
{
lean_object* v_code_2809_; 
v_code_2809_ = lean_ctor_get(v___x_2808_, 2);
lean_inc_ref(v_code_2809_);
v___y_2793_ = v_code_2809_;
goto v___jp_2792_;
}
case 1:
{
lean_object* v_code_2810_; 
v_code_2810_ = lean_ctor_get(v___x_2808_, 1);
lean_inc_ref(v_code_2810_);
v___y_2793_ = v_code_2810_;
goto v___jp_2792_;
}
default: 
{
lean_object* v_code_2811_; 
v_code_2811_ = lean_ctor_get(v___x_2808_, 0);
lean_inc_ref(v_code_2811_);
v___y_2793_ = v_code_2811_;
goto v___jp_2792_;
}
}
v___jp_2792_:
{
lean_object* v___x_2794_; 
lean_inc_ref(v_f_2781_);
v___x_2794_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2780_, v_f_2781_, v___y_2793_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2807_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2797_ = v___x_2794_;
v_isShared_2798_ = v_isSharedCheck_2807_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2794_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2807_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
uint8_t v___x_2799_; 
v___x_2799_ = lean_unbox(v_a_2795_);
lean_dec(v_a_2795_);
if (v___x_2799_ == 0)
{
size_t v___x_2800_; size_t v___x_2801_; 
lean_del_object(v___x_2797_);
v___x_2800_ = ((size_t)1ULL);
v___x_2801_ = lean_usize_add(v_i_2783_, v___x_2800_);
v_i_2783_ = v___x_2801_;
goto _start;
}
else
{
lean_object* v___x_2803_; lean_object* v___x_2805_; 
lean_dec_ref(v_f_2781_);
v___x_2803_ = lean_box(v___x_2791_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 0, v___x_2803_);
v___x_2805_ = v___x_2797_;
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
}
}
else
{
lean_dec_ref(v_f_2781_);
return v___x_2794_;
}
}
}
else
{
uint8_t v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
lean_dec_ref(v_f_2781_);
v___x_2812_ = 0;
v___x_2813_ = lean_box(v___x_2812_);
v___x_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
return v___x_2814_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0___boxed(lean_object* v_pu_2815_, lean_object* v_f_2816_, lean_object* v_as_2817_, lean_object* v_i_2818_, lean_object* v_stop_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
uint8_t v_pu_boxed_2825_; size_t v_i_boxed_2826_; size_t v_stop_boxed_2827_; lean_object* v_res_2828_; 
v_pu_boxed_2825_ = lean_unbox(v_pu_2815_);
v_i_boxed_2826_ = lean_unbox_usize(v_i_2818_);
lean_dec(v_i_2818_);
v_stop_boxed_2827_ = lean_unbox_usize(v_stop_2819_);
lean_dec(v_stop_2819_);
v_res_2828_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(v_pu_boxed_2825_, v_f_2816_, v_as_2817_, v_i_boxed_2826_, v_stop_boxed_2827_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec_ref(v_as_2817_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go___boxed(lean_object* v_pu_2829_, lean_object* v_f_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_){
_start:
{
uint8_t v_pu_boxed_2837_; lean_object* v_res_2838_; 
v_pu_boxed_2837_ = lean_unbox(v_pu_2829_);
v_res_2838_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_boxed_2837_, v_f_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(uint8_t v_pu_2839_, lean_object* v_f_2840_, lean_object* v_as_2841_, size_t v_i_2842_, size_t v_stop_2843_, lean_object* v_b_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v_a_2851_; uint8_t v___x_2855_; 
v___x_2855_ = lean_usize_dec_eq(v_i_2842_, v_stop_2843_);
if (v___x_2855_ == 0)
{
lean_object* v___x_2856_; lean_object* v_value_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2856_ = lean_array_uget_borrowed(v_as_2841_, v_i_2842_);
v_value_2857_ = lean_ctor_get(v___x_2856_, 1);
v___x_2858_ = lean_box(v_pu_2839_);
lean_inc_ref(v_f_2840_);
v___x_2859_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go___boxed), 8, 2);
lean_closure_set(v___x_2859_, 0, v___x_2858_);
lean_closure_set(v___x_2859_, 1, v_f_2840_);
lean_inc_ref(v_value_2857_);
v___x_2860_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2857_, v___x_2859_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; uint8_t v___x_2862_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref_known(v___x_2860_, 1);
v___x_2862_ = lean_unbox(v_a_2861_);
lean_dec(v_a_2861_);
if (v___x_2862_ == 0)
{
v_a_2851_ = v_b_2844_;
goto v___jp_2850_;
}
else
{
lean_object* v___x_2863_; 
lean_inc(v___x_2856_);
v___x_2863_ = lean_array_push(v_b_2844_, v___x_2856_);
v_a_2851_ = v___x_2863_;
goto v___jp_2850_;
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec_ref(v_b_2844_);
lean_dec_ref(v_f_2840_);
v_a_2864_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2860_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2860_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
else
{
lean_object* v___x_2872_; 
lean_dec_ref(v_f_2840_);
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v_b_2844_);
return v___x_2872_;
}
v___jp_2850_:
{
size_t v___x_2852_; size_t v___x_2853_; 
v___x_2852_ = ((size_t)1ULL);
v___x_2853_ = lean_usize_add(v_i_2842_, v___x_2852_);
v_i_2842_ = v___x_2853_;
v_b_2844_ = v_a_2851_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0___boxed(lean_object* v_pu_2873_, lean_object* v_f_2874_, lean_object* v_as_2875_, lean_object* v_i_2876_, lean_object* v_stop_2877_, lean_object* v_b_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
uint8_t v_pu_boxed_2884_; size_t v_i_boxed_2885_; size_t v_stop_boxed_2886_; lean_object* v_res_2887_; 
v_pu_boxed_2884_ = lean_unbox(v_pu_2873_);
v_i_boxed_2885_ = lean_unbox_usize(v_i_2876_);
lean_dec(v_i_2876_);
v_stop_boxed_2886_ = lean_unbox_usize(v_stop_2877_);
lean_dec(v_stop_2877_);
v_res_2887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_boxed_2884_, v_f_2874_, v_as_2875_, v_i_boxed_2885_, v_stop_boxed_2886_, v_b_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec_ref(v_as_2875_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByUnreach(uint8_t v_pu_2888_, lean_object* v_f_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; uint8_t v___x_2899_; 
v___x_2896_ = lean_unsigned_to_nat(0u);
v___x_2897_ = lean_array_get_size(v_a_2890_);
v___x_2898_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2899_ = lean_nat_dec_lt(v___x_2896_, v___x_2897_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; 
lean_dec_ref(v_f_2889_);
v___x_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2898_);
return v___x_2900_;
}
else
{
size_t v___x_2901_; size_t v___x_2902_; lean_object* v___x_2903_; 
v___x_2901_ = ((size_t)0ULL);
v___x_2902_ = lean_usize_of_nat(v___x_2897_);
v___x_2903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_2888_, v_f_2889_, v_a_2890_, v___x_2901_, v___x_2902_, v___x_2898_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_);
return v___x_2903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByUnreach___boxed(lean_object* v_pu_2904_, lean_object* v_f_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_){
_start:
{
uint8_t v_pu_boxed_2912_; lean_object* v_res_2913_; 
v_pu_boxed_2912_ = lean_unbox(v_pu_2904_);
v_res_2913_ = l_Lean_Compiler_LCNF_Probe_filterByUnreach(v_pu_boxed_2912_, v_f_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_);
lean_dec(v_a_2910_);
lean_dec_ref(v_a_2909_);
lean_dec(v_a_2908_);
lean_dec_ref(v_a_2907_);
lean_dec_ref(v_a_2906_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0(lean_object* v_decl_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_toSignature_2920_; lean_object* v_name_2921_; lean_object* v___x_2922_; 
v_toSignature_2920_ = lean_ctor_get(v_decl_2914_, 0);
v_name_2921_ = lean_ctor_get(v_toSignature_2920_, 0);
lean_inc(v_name_2921_);
v___x_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2922_, 0, v_name_2921_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0___boxed(lean_object* v_decl_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0(v_decl_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec_ref(v_decl_2923_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg(lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v___x_2937_; lean_object* v_toApplicative_2938_; lean_object* v_toFunctor_2939_; lean_object* v_toSeq_2940_; lean_object* v_toSeqLeft_2941_; lean_object* v_toSeqRight_2942_; lean_object* v___f_2943_; lean_object* v___f_2944_; lean_object* v___f_2945_; lean_object* v___f_2946_; lean_object* v___x_2947_; lean_object* v___f_2948_; lean_object* v___f_2949_; lean_object* v___f_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v_toApplicative_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2986_; 
v___x_2937_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_2938_ = lean_ctor_get(v___x_2937_, 0);
v_toFunctor_2939_ = lean_ctor_get(v_toApplicative_2938_, 0);
v_toSeq_2940_ = lean_ctor_get(v_toApplicative_2938_, 2);
v_toSeqLeft_2941_ = lean_ctor_get(v_toApplicative_2938_, 3);
v_toSeqRight_2942_ = lean_ctor_get(v_toApplicative_2938_, 4);
v___f_2943_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_2944_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2939_, 2);
v___f_2945_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2945_, 0, v_toFunctor_2939_);
v___f_2946_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2946_, 0, v_toFunctor_2939_);
v___x_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___f_2945_);
lean_ctor_set(v___x_2947_, 1, v___f_2946_);
lean_inc(v_toSeqRight_2942_);
v___f_2948_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2948_, 0, v_toSeqRight_2942_);
lean_inc(v_toSeqLeft_2941_);
v___f_2949_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2949_, 0, v_toSeqLeft_2941_);
lean_inc(v_toSeq_2940_);
v___f_2950_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2950_, 0, v_toSeq_2940_);
v___x_2951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2947_);
lean_ctor_set(v___x_2951_, 1, v___f_2943_);
lean_ctor_set(v___x_2951_, 2, v___f_2950_);
lean_ctor_set(v___x_2951_, 3, v___f_2949_);
lean_ctor_set(v___x_2951_, 4, v___f_2948_);
v___x_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
lean_ctor_set(v___x_2952_, 1, v___f_2944_);
v___x_2953_ = l_StateRefT_x27_instMonad___redArg(v___x_2952_);
v_toApplicative_2954_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2986_ == 0)
{
lean_object* v_unused_2987_; 
v_unused_2987_ = lean_ctor_get(v___x_2953_, 1);
lean_dec(v_unused_2987_);
v___x_2956_ = v___x_2953_;
v_isShared_2957_ = v_isSharedCheck_2986_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_toApplicative_2954_);
lean_dec(v___x_2953_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2986_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v_toFunctor_2958_; lean_object* v_toSeq_2959_; lean_object* v_toSeqLeft_2960_; lean_object* v_toSeqRight_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2984_; 
v_toFunctor_2958_ = lean_ctor_get(v_toApplicative_2954_, 0);
v_toSeq_2959_ = lean_ctor_get(v_toApplicative_2954_, 2);
v_toSeqLeft_2960_ = lean_ctor_get(v_toApplicative_2954_, 3);
v_toSeqRight_2961_ = lean_ctor_get(v_toApplicative_2954_, 4);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_toApplicative_2954_);
if (v_isSharedCheck_2984_ == 0)
{
lean_object* v_unused_2985_; 
v_unused_2985_ = lean_ctor_get(v_toApplicative_2954_, 1);
lean_dec(v_unused_2985_);
v___x_2963_ = v_toApplicative_2954_;
v_isShared_2964_ = v_isSharedCheck_2984_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_toSeqRight_2961_);
lean_inc(v_toSeqLeft_2960_);
lean_inc(v_toSeq_2959_);
lean_inc(v_toFunctor_2958_);
lean_dec(v_toApplicative_2954_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2984_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___f_2965_; lean_object* v___f_2966_; lean_object* v___f_2967_; lean_object* v___f_2968_; lean_object* v___f_2969_; lean_object* v___x_2970_; lean_object* v___f_2971_; lean_object* v___f_2972_; lean_object* v___f_2973_; lean_object* v___x_2975_; 
v___f_2965_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0));
v___f_2966_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_2967_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_2958_);
v___f_2968_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2968_, 0, v_toFunctor_2958_);
v___f_2969_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2969_, 0, v_toFunctor_2958_);
v___x_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___f_2968_);
lean_ctor_set(v___x_2970_, 1, v___f_2969_);
v___f_2971_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2971_, 0, v_toSeqRight_2961_);
v___f_2972_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2972_, 0, v_toSeqLeft_2960_);
v___f_2973_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2973_, 0, v_toSeq_2959_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 4, v___f_2971_);
lean_ctor_set(v___x_2963_, 3, v___f_2972_);
lean_ctor_set(v___x_2963_, 2, v___f_2973_);
lean_ctor_set(v___x_2963_, 1, v___f_2966_);
lean_ctor_set(v___x_2963_, 0, v___x_2970_);
v___x_2975_ = v___x_2963_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2970_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v___f_2966_);
lean_ctor_set(v_reuseFailAlloc_2983_, 2, v___f_2973_);
lean_ctor_set(v_reuseFailAlloc_2983_, 3, v___f_2972_);
lean_ctor_set(v_reuseFailAlloc_2983_, 4, v___f_2971_);
v___x_2975_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2977_; 
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 1, v___f_2967_);
lean_ctor_set(v___x_2956_, 0, v___x_2975_);
v___x_2977_ = v___x_2956_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___x_2975_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v___f_2967_);
v___x_2977_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
size_t v_sz_2978_; size_t v___x_2979_; lean_object* v___x_127__overap_2980_; lean_object* v___x_2981_; 
v_sz_2978_ = lean_array_size(v_a_2931_);
v___x_2979_ = ((size_t)0ULL);
v___x_127__overap_2980_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2977_, v___f_2965_, v_sz_2978_, v___x_2979_, v_a_2931_);
lean_inc(v_a_2935_);
lean_inc_ref(v_a_2934_);
lean_inc(v_a_2933_);
lean_inc_ref(v_a_2932_);
v___x_2981_ = lean_apply_5(v___x_127__overap_2980_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, lean_box(0));
return v___x_2981_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___boxed(lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_Lean_Compiler_LCNF_Probe_declNames___redArg(v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_);
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames(uint8_t v_pu_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_){
_start:
{
lean_object* v___x_3002_; lean_object* v_toApplicative_3003_; lean_object* v_toFunctor_3004_; lean_object* v_toSeq_3005_; lean_object* v_toSeqLeft_3006_; lean_object* v_toSeqRight_3007_; lean_object* v___f_3008_; lean_object* v___f_3009_; lean_object* v___f_3010_; lean_object* v___f_3011_; lean_object* v___x_3012_; lean_object* v___f_3013_; lean_object* v___f_3014_; lean_object* v___f_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v_toApplicative_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3051_; 
v___x_3002_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3003_ = lean_ctor_get(v___x_3002_, 0);
v_toFunctor_3004_ = lean_ctor_get(v_toApplicative_3003_, 0);
v_toSeq_3005_ = lean_ctor_get(v_toApplicative_3003_, 2);
v_toSeqLeft_3006_ = lean_ctor_get(v_toApplicative_3003_, 3);
v_toSeqRight_3007_ = lean_ctor_get(v_toApplicative_3003_, 4);
v___f_3008_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3009_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3004_, 2);
v___f_3010_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3010_, 0, v_toFunctor_3004_);
v___f_3011_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3011_, 0, v_toFunctor_3004_);
v___x_3012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___f_3010_);
lean_ctor_set(v___x_3012_, 1, v___f_3011_);
lean_inc(v_toSeqRight_3007_);
v___f_3013_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3013_, 0, v_toSeqRight_3007_);
lean_inc(v_toSeqLeft_3006_);
v___f_3014_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3014_, 0, v_toSeqLeft_3006_);
lean_inc(v_toSeq_3005_);
v___f_3015_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3015_, 0, v_toSeq_3005_);
v___x_3016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3012_);
lean_ctor_set(v___x_3016_, 1, v___f_3008_);
lean_ctor_set(v___x_3016_, 2, v___f_3015_);
lean_ctor_set(v___x_3016_, 3, v___f_3014_);
lean_ctor_set(v___x_3016_, 4, v___f_3013_);
v___x_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
lean_ctor_set(v___x_3017_, 1, v___f_3009_);
v___x_3018_ = l_StateRefT_x27_instMonad___redArg(v___x_3017_);
v_toApplicative_3019_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3051_ == 0)
{
lean_object* v_unused_3052_; 
v_unused_3052_ = lean_ctor_get(v___x_3018_, 1);
lean_dec(v_unused_3052_);
v___x_3021_ = v___x_3018_;
v_isShared_3022_ = v_isSharedCheck_3051_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_toApplicative_3019_);
lean_dec(v___x_3018_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3051_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v_toFunctor_3023_; lean_object* v_toSeq_3024_; lean_object* v_toSeqLeft_3025_; lean_object* v_toSeqRight_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3049_; 
v_toFunctor_3023_ = lean_ctor_get(v_toApplicative_3019_, 0);
v_toSeq_3024_ = lean_ctor_get(v_toApplicative_3019_, 2);
v_toSeqLeft_3025_ = lean_ctor_get(v_toApplicative_3019_, 3);
v_toSeqRight_3026_ = lean_ctor_get(v_toApplicative_3019_, 4);
v_isSharedCheck_3049_ = !lean_is_exclusive(v_toApplicative_3019_);
if (v_isSharedCheck_3049_ == 0)
{
lean_object* v_unused_3050_; 
v_unused_3050_ = lean_ctor_get(v_toApplicative_3019_, 1);
lean_dec(v_unused_3050_);
v___x_3028_ = v_toApplicative_3019_;
v_isShared_3029_ = v_isSharedCheck_3049_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_toSeqRight_3026_);
lean_inc(v_toSeqLeft_3025_);
lean_inc(v_toSeq_3024_);
lean_inc(v_toFunctor_3023_);
lean_dec(v_toApplicative_3019_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3049_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___f_3030_; lean_object* v___f_3031_; lean_object* v___f_3032_; lean_object* v___f_3033_; lean_object* v___f_3034_; lean_object* v___x_3035_; lean_object* v___f_3036_; lean_object* v___f_3037_; lean_object* v___f_3038_; lean_object* v___x_3040_; 
v___f_3030_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0));
v___f_3031_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3032_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3023_);
v___f_3033_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3033_, 0, v_toFunctor_3023_);
v___f_3034_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3034_, 0, v_toFunctor_3023_);
v___x_3035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3035_, 0, v___f_3033_);
lean_ctor_set(v___x_3035_, 1, v___f_3034_);
v___f_3036_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3036_, 0, v_toSeqRight_3026_);
v___f_3037_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3037_, 0, v_toSeqLeft_3025_);
v___f_3038_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3038_, 0, v_toSeq_3024_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 4, v___f_3036_);
lean_ctor_set(v___x_3028_, 3, v___f_3037_);
lean_ctor_set(v___x_3028_, 2, v___f_3038_);
lean_ctor_set(v___x_3028_, 1, v___f_3031_);
lean_ctor_set(v___x_3028_, 0, v___x_3035_);
v___x_3040_ = v___x_3028_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3035_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v___f_3031_);
lean_ctor_set(v_reuseFailAlloc_3048_, 2, v___f_3038_);
lean_ctor_set(v_reuseFailAlloc_3048_, 3, v___f_3037_);
lean_ctor_set(v_reuseFailAlloc_3048_, 4, v___f_3036_);
v___x_3040_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3042_; 
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 1, v___f_3032_);
lean_ctor_set(v___x_3021_, 0, v___x_3040_);
v___x_3042_ = v___x_3021_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3040_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v___f_3032_);
v___x_3042_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
size_t v_sz_3043_; size_t v___x_3044_; lean_object* v___x_185__overap_3045_; lean_object* v___x_3046_; 
v_sz_3043_ = lean_array_size(v_a_2996_);
v___x_3044_ = ((size_t)0ULL);
v___x_185__overap_3045_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3042_, v___f_3030_, v_sz_3043_, v___x_3044_, v_a_2996_);
lean_inc(v_a_3000_);
lean_inc_ref(v_a_2999_);
lean_inc(v_a_2998_);
lean_inc_ref(v_a_2997_);
v___x_3046_ = lean_apply_5(v___x_185__overap_3045_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_, lean_box(0));
return v___x_3046_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___boxed(lean_object* v_pu_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_){
_start:
{
uint8_t v_pu_boxed_3060_; lean_object* v_res_3061_; 
v_pu_boxed_3060_ = lean_unbox(v_pu_3053_);
v_res_3061_ = l_Lean_Compiler_LCNF_Probe_declNames(v_pu_boxed_3060_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_);
lean_dec(v_a_3058_);
lean_dec_ref(v_a_3057_);
lean_dec(v_a_3056_);
lean_dec_ref(v_a_3055_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0(lean_object* v_inst_3062_, lean_object* v_x_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = lean_apply_1(v_inst_3062_, v_x_3063_);
v___x_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed(lean_object* v_inst_3071_, lean_object* v_x_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0(v_inst_3071_, v_x_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg(lean_object* v_inst_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v___x_3086_; lean_object* v_toApplicative_3087_; lean_object* v_toFunctor_3088_; lean_object* v_toSeq_3089_; lean_object* v_toSeqLeft_3090_; lean_object* v_toSeqRight_3091_; lean_object* v___f_3092_; lean_object* v___f_3093_; lean_object* v___f_3094_; lean_object* v___f_3095_; lean_object* v___x_3096_; lean_object* v___f_3097_; lean_object* v___f_3098_; lean_object* v___f_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v_toApplicative_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3135_; 
v___x_3086_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3087_ = lean_ctor_get(v___x_3086_, 0);
v_toFunctor_3088_ = lean_ctor_get(v_toApplicative_3087_, 0);
v_toSeq_3089_ = lean_ctor_get(v_toApplicative_3087_, 2);
v_toSeqLeft_3090_ = lean_ctor_get(v_toApplicative_3087_, 3);
v_toSeqRight_3091_ = lean_ctor_get(v_toApplicative_3087_, 4);
v___f_3092_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3093_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3088_, 2);
v___f_3094_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3094_, 0, v_toFunctor_3088_);
v___f_3095_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3095_, 0, v_toFunctor_3088_);
v___x_3096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___f_3094_);
lean_ctor_set(v___x_3096_, 1, v___f_3095_);
lean_inc(v_toSeqRight_3091_);
v___f_3097_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3097_, 0, v_toSeqRight_3091_);
lean_inc(v_toSeqLeft_3090_);
v___f_3098_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3098_, 0, v_toSeqLeft_3090_);
lean_inc(v_toSeq_3089_);
v___f_3099_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3099_, 0, v_toSeq_3089_);
v___x_3100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3096_);
lean_ctor_set(v___x_3100_, 1, v___f_3092_);
lean_ctor_set(v___x_3100_, 2, v___f_3099_);
lean_ctor_set(v___x_3100_, 3, v___f_3098_);
lean_ctor_set(v___x_3100_, 4, v___f_3097_);
v___x_3101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3100_);
lean_ctor_set(v___x_3101_, 1, v___f_3093_);
v___x_3102_ = l_StateRefT_x27_instMonad___redArg(v___x_3101_);
v_toApplicative_3103_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3135_ == 0)
{
lean_object* v_unused_3136_; 
v_unused_3136_ = lean_ctor_get(v___x_3102_, 1);
lean_dec(v_unused_3136_);
v___x_3105_ = v___x_3102_;
v_isShared_3106_ = v_isSharedCheck_3135_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_toApplicative_3103_);
lean_dec(v___x_3102_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3135_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v_toFunctor_3107_; lean_object* v_toSeq_3108_; lean_object* v_toSeqLeft_3109_; lean_object* v_toSeqRight_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3133_; 
v_toFunctor_3107_ = lean_ctor_get(v_toApplicative_3103_, 0);
v_toSeq_3108_ = lean_ctor_get(v_toApplicative_3103_, 2);
v_toSeqLeft_3109_ = lean_ctor_get(v_toApplicative_3103_, 3);
v_toSeqRight_3110_ = lean_ctor_get(v_toApplicative_3103_, 4);
v_isSharedCheck_3133_ = !lean_is_exclusive(v_toApplicative_3103_);
if (v_isSharedCheck_3133_ == 0)
{
lean_object* v_unused_3134_; 
v_unused_3134_ = lean_ctor_get(v_toApplicative_3103_, 1);
lean_dec(v_unused_3134_);
v___x_3112_ = v_toApplicative_3103_;
v_isShared_3113_ = v_isSharedCheck_3133_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_toSeqRight_3110_);
lean_inc(v_toSeqLeft_3109_);
lean_inc(v_toSeq_3108_);
lean_inc(v_toFunctor_3107_);
lean_dec(v_toApplicative_3103_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3133_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___f_3114_; lean_object* v___f_3115_; lean_object* v___f_3116_; lean_object* v___f_3117_; lean_object* v___f_3118_; lean_object* v___x_3119_; lean_object* v___f_3120_; lean_object* v___f_3121_; lean_object* v___f_3122_; lean_object* v___x_3124_; 
v___f_3114_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3114_, 0, v_inst_3079_);
v___f_3115_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3116_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3107_);
v___f_3117_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3117_, 0, v_toFunctor_3107_);
v___f_3118_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3118_, 0, v_toFunctor_3107_);
v___x_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3119_, 0, v___f_3117_);
lean_ctor_set(v___x_3119_, 1, v___f_3118_);
v___f_3120_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3120_, 0, v_toSeqRight_3110_);
v___f_3121_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3121_, 0, v_toSeqLeft_3109_);
v___f_3122_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3122_, 0, v_toSeq_3108_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 4, v___f_3120_);
lean_ctor_set(v___x_3112_, 3, v___f_3121_);
lean_ctor_set(v___x_3112_, 2, v___f_3122_);
lean_ctor_set(v___x_3112_, 1, v___f_3115_);
lean_ctor_set(v___x_3112_, 0, v___x_3119_);
v___x_3124_ = v___x_3112_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v___x_3119_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v___f_3115_);
lean_ctor_set(v_reuseFailAlloc_3132_, 2, v___f_3122_);
lean_ctor_set(v_reuseFailAlloc_3132_, 3, v___f_3121_);
lean_ctor_set(v_reuseFailAlloc_3132_, 4, v___f_3120_);
v___x_3124_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
lean_object* v___x_3126_; 
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 1, v___f_3116_);
lean_ctor_set(v___x_3105_, 0, v___x_3124_);
v___x_3126_ = v___x_3105_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3124_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v___f_3116_);
v___x_3126_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
size_t v_sz_3127_; size_t v___x_3128_; lean_object* v___x_129__overap_3129_; lean_object* v___x_3130_; 
v_sz_3127_ = lean_array_size(v_a_3080_);
v___x_3128_ = ((size_t)0ULL);
v___x_129__overap_3129_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3126_, v___f_3114_, v_sz_3127_, v___x_3128_, v_a_3080_);
lean_inc(v_a_3084_);
lean_inc_ref(v_a_3083_);
lean_inc(v_a_3082_);
lean_inc_ref(v_a_3081_);
v___x_3130_ = lean_apply_5(v___x_129__overap_3129_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, lean_box(0));
return v___x_3130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___boxed(lean_object* v_inst_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_Lean_Compiler_LCNF_Probe_toString___redArg(v_inst_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_);
lean_dec(v_a_3142_);
lean_dec_ref(v_a_3141_);
lean_dec(v_a_3140_);
lean_dec_ref(v_a_3139_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString(lean_object* v_00_u03b1_3145_, lean_object* v_inst_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_){
_start:
{
lean_object* v___x_3153_; lean_object* v_toApplicative_3154_; lean_object* v_toFunctor_3155_; lean_object* v_toSeq_3156_; lean_object* v_toSeqLeft_3157_; lean_object* v_toSeqRight_3158_; lean_object* v___f_3159_; lean_object* v___f_3160_; lean_object* v___f_3161_; lean_object* v___f_3162_; lean_object* v___x_3163_; lean_object* v___f_3164_; lean_object* v___f_3165_; lean_object* v___f_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v_toApplicative_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3202_; 
v___x_3153_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3154_ = lean_ctor_get(v___x_3153_, 0);
v_toFunctor_3155_ = lean_ctor_get(v_toApplicative_3154_, 0);
v_toSeq_3156_ = lean_ctor_get(v_toApplicative_3154_, 2);
v_toSeqLeft_3157_ = lean_ctor_get(v_toApplicative_3154_, 3);
v_toSeqRight_3158_ = lean_ctor_get(v_toApplicative_3154_, 4);
v___f_3159_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3160_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3155_, 2);
v___f_3161_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3161_, 0, v_toFunctor_3155_);
v___f_3162_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3162_, 0, v_toFunctor_3155_);
v___x_3163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___f_3161_);
lean_ctor_set(v___x_3163_, 1, v___f_3162_);
lean_inc(v_toSeqRight_3158_);
v___f_3164_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3164_, 0, v_toSeqRight_3158_);
lean_inc(v_toSeqLeft_3157_);
v___f_3165_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3165_, 0, v_toSeqLeft_3157_);
lean_inc(v_toSeq_3156_);
v___f_3166_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3166_, 0, v_toSeq_3156_);
v___x_3167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3163_);
lean_ctor_set(v___x_3167_, 1, v___f_3159_);
lean_ctor_set(v___x_3167_, 2, v___f_3166_);
lean_ctor_set(v___x_3167_, 3, v___f_3165_);
lean_ctor_set(v___x_3167_, 4, v___f_3164_);
v___x_3168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
lean_ctor_set(v___x_3168_, 1, v___f_3160_);
v___x_3169_ = l_StateRefT_x27_instMonad___redArg(v___x_3168_);
v_toApplicative_3170_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3202_ == 0)
{
lean_object* v_unused_3203_; 
v_unused_3203_ = lean_ctor_get(v___x_3169_, 1);
lean_dec(v_unused_3203_);
v___x_3172_ = v___x_3169_;
v_isShared_3173_ = v_isSharedCheck_3202_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_toApplicative_3170_);
lean_dec(v___x_3169_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3202_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v_toFunctor_3174_; lean_object* v_toSeq_3175_; lean_object* v_toSeqLeft_3176_; lean_object* v_toSeqRight_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3200_; 
v_toFunctor_3174_ = lean_ctor_get(v_toApplicative_3170_, 0);
v_toSeq_3175_ = lean_ctor_get(v_toApplicative_3170_, 2);
v_toSeqLeft_3176_ = lean_ctor_get(v_toApplicative_3170_, 3);
v_toSeqRight_3177_ = lean_ctor_get(v_toApplicative_3170_, 4);
v_isSharedCheck_3200_ = !lean_is_exclusive(v_toApplicative_3170_);
if (v_isSharedCheck_3200_ == 0)
{
lean_object* v_unused_3201_; 
v_unused_3201_ = lean_ctor_get(v_toApplicative_3170_, 1);
lean_dec(v_unused_3201_);
v___x_3179_ = v_toApplicative_3170_;
v_isShared_3180_ = v_isSharedCheck_3200_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_toSeqRight_3177_);
lean_inc(v_toSeqLeft_3176_);
lean_inc(v_toSeq_3175_);
lean_inc(v_toFunctor_3174_);
lean_dec(v_toApplicative_3170_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3200_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___f_3181_; lean_object* v___f_3182_; lean_object* v___f_3183_; lean_object* v___f_3184_; lean_object* v___f_3185_; lean_object* v___x_3186_; lean_object* v___f_3187_; lean_object* v___f_3188_; lean_object* v___f_3189_; lean_object* v___x_3191_; 
v___f_3181_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3181_, 0, v_inst_3146_);
v___f_3182_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3183_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3174_);
v___f_3184_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3184_, 0, v_toFunctor_3174_);
v___f_3185_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3185_, 0, v_toFunctor_3174_);
v___x_3186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___f_3184_);
lean_ctor_set(v___x_3186_, 1, v___f_3185_);
v___f_3187_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3187_, 0, v_toSeqRight_3177_);
v___f_3188_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3188_, 0, v_toSeqLeft_3176_);
v___f_3189_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3189_, 0, v_toSeq_3175_);
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 4, v___f_3187_);
lean_ctor_set(v___x_3179_, 3, v___f_3188_);
lean_ctor_set(v___x_3179_, 2, v___f_3189_);
lean_ctor_set(v___x_3179_, 1, v___f_3182_);
lean_ctor_set(v___x_3179_, 0, v___x_3186_);
v___x_3191_ = v___x_3179_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3186_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v___f_3182_);
lean_ctor_set(v_reuseFailAlloc_3199_, 2, v___f_3189_);
lean_ctor_set(v_reuseFailAlloc_3199_, 3, v___f_3188_);
lean_ctor_set(v_reuseFailAlloc_3199_, 4, v___f_3187_);
v___x_3191_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
lean_object* v___x_3193_; 
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 1, v___f_3183_);
lean_ctor_set(v___x_3172_, 0, v___x_3191_);
v___x_3193_ = v___x_3172_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3191_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v___f_3183_);
v___x_3193_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
size_t v_sz_3194_; size_t v___x_3195_; lean_object* v___x_190__overap_3196_; lean_object* v___x_3197_; 
v_sz_3194_ = lean_array_size(v_a_3147_);
v___x_3195_ = ((size_t)0ULL);
v___x_190__overap_3196_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3193_, v___f_3181_, v_sz_3194_, v___x_3195_, v_a_3147_);
lean_inc(v_a_3151_);
lean_inc_ref(v_a_3150_);
lean_inc(v_a_3149_);
lean_inc_ref(v_a_3148_);
v___x_3197_ = lean_apply_5(v___x_190__overap_3196_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_, lean_box(0));
return v___x_3197_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___boxed(lean_object* v_00_u03b1_3204_, lean_object* v_inst_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Lean_Compiler_LCNF_Probe_toString(v_00_u03b1_3204_, v_inst_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_);
lean_dec(v_a_3210_);
lean_dec_ref(v_a_3209_);
lean_dec(v_a_3208_);
lean_dec_ref(v_a_3207_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___redArg(lean_object* v_data_3213_){
_start:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3215_ = lean_array_get_size(v_data_3213_);
v___x_3216_ = lean_unsigned_to_nat(1u);
v___x_3217_ = lean_mk_empty_array_with_capacity(v___x_3216_);
v___x_3218_ = lean_array_push(v___x_3217_, v___x_3215_);
v___x_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___redArg___boxed(lean_object* v_data_3220_, lean_object* v_a_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Lean_Compiler_LCNF_Probe_count___redArg(v_data_3220_);
lean_dec_ref(v_data_3220_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count(lean_object* v_00_u03b1_3223_, lean_object* v_data_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3230_ = lean_array_get_size(v_data_3224_);
v___x_3231_ = lean_unsigned_to_nat(1u);
v___x_3232_ = lean_mk_empty_array_with_capacity(v___x_3231_);
v___x_3233_ = lean_array_push(v___x_3232_, v___x_3230_);
v___x_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3233_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___boxed(lean_object* v_00_u03b1_3235_, lean_object* v_data_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_){
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l_Lean_Compiler_LCNF_Probe_count(v_00_u03b1_3235_, v_data_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_);
lean_dec(v_a_3240_);
lean_dec_ref(v_a_3239_);
lean_dec(v_a_3238_);
lean_dec_ref(v_a_3237_);
lean_dec_ref(v_data_3236_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___redArg(lean_object* v_data_3244_){
_start:
{
lean_object* v___y_3247_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; uint8_t v___x_3255_; 
v___x_3252_ = lean_unsigned_to_nat(0u);
v___x_3253_ = lean_array_get_size(v_data_3244_);
v___x_3254_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v___x_3255_ = lean_nat_dec_lt(v___x_3252_, v___x_3253_);
if (v___x_3255_ == 0)
{
lean_dec_ref(v_data_3244_);
v___y_3247_ = v___x_3252_;
goto v___jp_3246_;
}
else
{
lean_object* v___f_3256_; size_t v___x_3257_; size_t v___x_3258_; lean_object* v___x_3259_; 
v___f_3256_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0));
v___x_3257_ = ((size_t)0ULL);
v___x_3258_ = lean_usize_of_nat(v___x_3253_);
v___x_3259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3254_, v___f_3256_, v_data_3244_, v___x_3257_, v___x_3258_, v___x_3252_);
v___y_3247_ = v___x_3259_;
goto v___jp_3246_;
}
v___jp_3246_:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3248_ = lean_unsigned_to_nat(1u);
v___x_3249_ = lean_mk_empty_array_with_capacity(v___x_3248_);
v___x_3250_ = lean_array_push(v___x_3249_, v___y_3247_);
v___x_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3250_);
return v___x_3251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___redArg___boxed(lean_object* v_data_3260_, lean_object* v_a_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Lean_Compiler_LCNF_Probe_sum___redArg(v_data_3260_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum(lean_object* v_data_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_){
_start:
{
lean_object* v___y_3270_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; uint8_t v___x_3278_; 
v___x_3275_ = lean_unsigned_to_nat(0u);
v___x_3276_ = lean_array_get_size(v_data_3263_);
v___x_3277_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v___x_3278_ = lean_nat_dec_lt(v___x_3275_, v___x_3276_);
if (v___x_3278_ == 0)
{
lean_dec_ref(v_data_3263_);
v___y_3270_ = v___x_3275_;
goto v___jp_3269_;
}
else
{
lean_object* v___f_3279_; size_t v___x_3280_; size_t v___x_3281_; lean_object* v___x_3282_; 
v___f_3279_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0));
v___x_3280_ = ((size_t)0ULL);
v___x_3281_ = lean_usize_of_nat(v___x_3276_);
v___x_3282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3277_, v___f_3279_, v_data_3263_, v___x_3280_, v___x_3281_, v___x_3275_);
v___y_3270_ = v___x_3282_;
goto v___jp_3269_;
}
v___jp_3269_:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3271_ = lean_unsigned_to_nat(1u);
v___x_3272_ = lean_mk_empty_array_with_capacity(v___x_3271_);
v___x_3273_ = lean_array_push(v___x_3272_, v___y_3270_);
v___x_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3273_);
return v___x_3274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___boxed(lean_object* v_data_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l_Lean_Compiler_LCNF_Probe_sum(v_data_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
lean_dec(v_a_3287_);
lean_dec_ref(v_a_3286_);
lean_dec(v_a_3285_);
lean_dec_ref(v_a_3284_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___redArg(lean_object* v_n_3290_, lean_object* v_data_3291_){
_start:
{
lean_object* v_lower_3294_; lean_object* v_upper_3295_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; uint8_t v___x_3302_; 
v___x_3299_ = lean_array_get_size(v_data_3291_);
v___x_3300_ = lean_nat_sub(v___x_3299_, v_n_3290_);
v___x_3301_ = lean_unsigned_to_nat(0u);
v___x_3302_ = lean_nat_dec_le(v___x_3300_, v___x_3301_);
if (v___x_3302_ == 0)
{
v_lower_3294_ = v___x_3300_;
v_upper_3295_ = v___x_3299_;
goto v___jp_3293_;
}
else
{
lean_dec(v___x_3300_);
v_lower_3294_ = v___x_3301_;
v_upper_3295_ = v___x_3299_;
goto v___jp_3293_;
}
v___jp_3293_:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3296_ = l_Array_toSubarray___redArg(v_data_3291_, v_lower_3294_, v_upper_3295_);
v___x_3297_ = l_Subarray_copy___redArg(v___x_3296_);
v___x_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
return v___x_3298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___redArg___boxed(lean_object* v_n_3303_, lean_object* v_data_3304_, lean_object* v_a_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Lean_Compiler_LCNF_Probe_tail___redArg(v_n_3303_, v_data_3304_);
lean_dec(v_n_3303_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail(lean_object* v_00_u03b1_3307_, lean_object* v_n_3308_, lean_object* v_data_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_){
_start:
{
lean_object* v_lower_3316_; lean_object* v_upper_3317_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; uint8_t v___x_3324_; 
v___x_3321_ = lean_array_get_size(v_data_3309_);
v___x_3322_ = lean_nat_sub(v___x_3321_, v_n_3308_);
v___x_3323_ = lean_unsigned_to_nat(0u);
v___x_3324_ = lean_nat_dec_le(v___x_3322_, v___x_3323_);
if (v___x_3324_ == 0)
{
v_lower_3316_ = v___x_3322_;
v_upper_3317_ = v___x_3321_;
goto v___jp_3315_;
}
else
{
lean_dec(v___x_3322_);
v_lower_3316_ = v___x_3323_;
v_upper_3317_ = v___x_3321_;
goto v___jp_3315_;
}
v___jp_3315_:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3318_ = l_Array_toSubarray___redArg(v_data_3309_, v_lower_3316_, v_upper_3317_);
v___x_3319_ = l_Subarray_copy___redArg(v___x_3318_);
v___x_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
return v___x_3320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___boxed(lean_object* v_00_u03b1_3325_, lean_object* v_n_3326_, lean_object* v_data_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l_Lean_Compiler_LCNF_Probe_tail(v_00_u03b1_3325_, v_n_3326_, v_data_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_);
lean_dec(v_a_3331_);
lean_dec_ref(v_a_3330_);
lean_dec(v_a_3329_);
lean_dec_ref(v_a_3328_);
lean_dec(v_n_3326_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___redArg(lean_object* v_n_3334_, lean_object* v_data_3335_){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3337_ = lean_unsigned_to_nat(0u);
v___x_3338_ = l_Array_toSubarray___redArg(v_data_3335_, v___x_3337_, v_n_3334_);
v___x_3339_ = l_Subarray_copy___redArg(v___x_3338_);
v___x_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3339_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___redArg___boxed(lean_object* v_n_3341_, lean_object* v_data_3342_, lean_object* v_a_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l_Lean_Compiler_LCNF_Probe_head___redArg(v_n_3341_, v_data_3342_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head(lean_object* v_00_u03b1_3345_, lean_object* v_n_3346_, lean_object* v_data_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3353_ = lean_unsigned_to_nat(0u);
v___x_3354_ = l_Array_toSubarray___redArg(v_data_3347_, v___x_3353_, v_n_3346_);
v___x_3355_ = l_Subarray_copy___redArg(v___x_3354_);
v___x_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___boxed(lean_object* v_00_u03b1_3357_, lean_object* v_n_3358_, lean_object* v_data_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l_Lean_Compiler_LCNF_Probe_head(v_00_u03b1_3357_, v_n_3358_, v_data_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
lean_dec(v_a_3361_);
lean_dec_ref(v_a_3360_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0(lean_object* v_probe_3371_, lean_object* v___x_3372_, lean_object* v_inst_3373_, lean_object* v___x_3374_, lean_object* v___x_3375_, lean_object* v_toMonadRef_3376_, lean_object* v___f_3377_, lean_object* v_decls_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v___x_3384_; 
lean_inc(v___y_3382_);
lean_inc_ref(v___y_3381_);
lean_inc(v___y_3380_);
lean_inc_ref(v___y_3379_);
lean_inc_ref(v_decls_3378_);
v___x_3384_ = lean_apply_6(v_probe_3371_, v_decls_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, lean_box(0));
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_toCold_3385_; lean_object* v_options_3386_; uint8_t v_hasTrace_3387_; 
v_toCold_3385_ = lean_ctor_get(v___y_3381_, 0);
v_options_3386_ = lean_ctor_get(v_toCold_3385_, 2);
v_hasTrace_3387_ = lean_ctor_get_uint8(v_options_3386_, sizeof(void*)*1);
if (v_hasTrace_3387_ == 0)
{
lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_dec_ref(v___f_3377_);
lean_dec_ref(v_toMonadRef_3376_);
lean_dec_ref(v___x_3375_);
lean_dec_ref(v___x_3374_);
lean_dec_ref(v_inst_3373_);
lean_dec_ref(v___x_3372_);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3394_ == 0)
{
lean_object* v_unused_3395_; 
v_unused_3395_ = lean_ctor_get(v___x_3384_, 0);
lean_dec(v_unused_3395_);
v___x_3389_ = v___x_3384_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_dec(v___x_3384_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 0, v_decls_3378_);
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_decls_3378_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3433_; 
v_a_3396_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3398_ = v___x_3384_;
v_isShared_3399_ = v_isSharedCheck_3433_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3384_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3433_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v_inheritedTraceOptions_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; uint8_t v___x_3405_; 
v_inheritedTraceOptions_3400_ = lean_ctor_get(v_toCold_3385_, 11);
v___x_3401_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0));
v___x_3402_ = l_Lean_Name_mkStr2(v___x_3401_, v___x_3372_);
v___x_3403_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__2));
lean_inc(v___x_3402_);
v___x_3404_ = l_Lean_Name_append(v___x_3403_, v___x_3402_);
v___x_3405_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3400_, v_options_3386_, v___x_3404_);
lean_dec(v___x_3404_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3407_; 
lean_dec(v___x_3402_);
lean_dec(v_a_3396_);
lean_dec_ref(v___f_3377_);
lean_dec_ref(v_toMonadRef_3376_);
lean_dec_ref(v___x_3375_);
lean_dec_ref(v___x_3374_);
lean_dec_ref(v_inst_3373_);
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 0, v_decls_3378_);
v___x_3407_ = v___x_3398_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_decls_3378_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
else
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_978__overap_3415_; lean_object* v___x_3416_; 
lean_del_object(v___x_3398_);
v___x_3409_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__3));
v___x_3410_ = lean_array_to_list(v_a_3396_);
v___x_3411_ = l_List_toString___redArg(v_inst_3373_, v___x_3410_);
v___x_3412_ = lean_string_append(v___x_3409_, v___x_3411_);
lean_dec_ref(v___x_3411_);
v___x_3413_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
v___x_3414_ = l_Lean_MessageData_ofFormat(v___x_3413_);
v___x_978__overap_3415_ = l_Lean_addTrace___redArg(v___x_3374_, v___x_3375_, v_toMonadRef_3376_, v___f_3377_, v___x_3402_, v___x_3414_);
lean_inc(v___y_3382_);
lean_inc_ref(v___y_3381_);
lean_inc(v___y_3380_);
lean_inc_ref(v___y_3379_);
v___x_3416_ = lean_apply_5(v___x_978__overap_3415_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, lean_box(0));
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3423_ == 0)
{
lean_object* v_unused_3424_; 
v_unused_3424_ = lean_ctor_get(v___x_3416_, 0);
lean_dec(v_unused_3424_);
v___x_3418_ = v___x_3416_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_dec(v___x_3416_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v_decls_3378_);
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_decls_3378_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
lean_dec_ref(v_decls_3378_);
v_a_3425_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v___x_3416_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3416_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3425_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec_ref(v_decls_3378_);
lean_dec_ref(v___f_3377_);
lean_dec_ref(v_toMonadRef_3376_);
lean_dec_ref(v___x_3375_);
lean_dec_ref(v___x_3374_);
lean_dec_ref(v_inst_3373_);
lean_dec_ref(v___x_3372_);
v_a_3434_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3384_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3384_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___boxed(lean_object* v_probe_3442_, lean_object* v___x_3443_, lean_object* v_inst_3444_, lean_object* v___x_3445_, lean_object* v___x_3446_, lean_object* v_toMonadRef_3447_, lean_object* v___f_3448_, lean_object* v_decls_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0(v_probe_3442_, v___x_3443_, v_inst_3444_, v___x_3445_, v___x_3446_, v_toMonadRef_3447_, v___f_3448_, v_decls_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
return v_res_3455_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2(void){
_start:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3458_ = l_Lean_Core_instMonadTraceCoreM;
v___x_3459_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1));
v___x_3460_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_3459_, v___x_3458_);
return v___x_3460_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3(void){
_start:
{
lean_object* v___x_3461_; lean_object* v___f_3462_; lean_object* v___x_3463_; 
v___x_3461_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2);
v___f_3462_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0));
v___x_3463_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3462_, v___x_3461_);
return v___x_3463_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6(void){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3466_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_3467_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1));
v___x_3468_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__5));
v___x_3469_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_3468_, v___x_3467_, v___x_3466_);
return v___x_3469_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7(void){
_start:
{
lean_object* v___x_3470_; lean_object* v___f_3471_; lean_object* v___f_3472_; lean_object* v___x_3473_; 
v___x_3470_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6);
v___f_3471_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0));
v___f_3472_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4));
v___x_3473_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_3472_, v___f_3471_, v___x_3470_);
return v___x_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg(lean_object* v_inst_3478_, uint8_t v_phase_3479_, lean_object* v_probe_3480_){
_start:
{
lean_object* v___x_3481_; lean_object* v_toApplicative_3482_; lean_object* v_toFunctor_3483_; lean_object* v_toSeq_3484_; lean_object* v_toSeqLeft_3485_; lean_object* v_toSeqRight_3486_; lean_object* v___f_3487_; lean_object* v___f_3488_; lean_object* v___f_3489_; lean_object* v___f_3490_; lean_object* v___x_3491_; lean_object* v___f_3492_; lean_object* v___f_3493_; lean_object* v___f_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v_toApplicative_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3535_; 
v___x_3481_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3482_ = lean_ctor_get(v___x_3481_, 0);
v_toFunctor_3483_ = lean_ctor_get(v_toApplicative_3482_, 0);
v_toSeq_3484_ = lean_ctor_get(v_toApplicative_3482_, 2);
v_toSeqLeft_3485_ = lean_ctor_get(v_toApplicative_3482_, 3);
v_toSeqRight_3486_ = lean_ctor_get(v_toApplicative_3482_, 4);
v___f_3487_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3488_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3483_, 2);
v___f_3489_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3489_, 0, v_toFunctor_3483_);
v___f_3490_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3490_, 0, v_toFunctor_3483_);
v___x_3491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___f_3489_);
lean_ctor_set(v___x_3491_, 1, v___f_3490_);
lean_inc(v_toSeqRight_3486_);
v___f_3492_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3492_, 0, v_toSeqRight_3486_);
lean_inc(v_toSeqLeft_3485_);
v___f_3493_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3493_, 0, v_toSeqLeft_3485_);
lean_inc(v_toSeq_3484_);
v___f_3494_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3494_, 0, v_toSeq_3484_);
v___x_3495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3491_);
lean_ctor_set(v___x_3495_, 1, v___f_3487_);
lean_ctor_set(v___x_3495_, 2, v___f_3494_);
lean_ctor_set(v___x_3495_, 3, v___f_3493_);
lean_ctor_set(v___x_3495_, 4, v___f_3492_);
v___x_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
lean_ctor_set(v___x_3496_, 1, v___f_3488_);
v___x_3497_ = l_StateRefT_x27_instMonad___redArg(v___x_3496_);
v_toApplicative_3498_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3535_ == 0)
{
lean_object* v_unused_3536_; 
v_unused_3536_ = lean_ctor_get(v___x_3497_, 1);
lean_dec(v_unused_3536_);
v___x_3500_ = v___x_3497_;
v_isShared_3501_ = v_isSharedCheck_3535_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_toApplicative_3498_);
lean_dec(v___x_3497_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3535_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v_toFunctor_3502_; lean_object* v_toSeq_3503_; lean_object* v_toSeqLeft_3504_; lean_object* v_toSeqRight_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3533_; 
v_toFunctor_3502_ = lean_ctor_get(v_toApplicative_3498_, 0);
v_toSeq_3503_ = lean_ctor_get(v_toApplicative_3498_, 2);
v_toSeqLeft_3504_ = lean_ctor_get(v_toApplicative_3498_, 3);
v_toSeqRight_3505_ = lean_ctor_get(v_toApplicative_3498_, 4);
v_isSharedCheck_3533_ = !lean_is_exclusive(v_toApplicative_3498_);
if (v_isSharedCheck_3533_ == 0)
{
lean_object* v_unused_3534_; 
v_unused_3534_ = lean_ctor_get(v_toApplicative_3498_, 1);
lean_dec(v_unused_3534_);
v___x_3507_ = v_toApplicative_3498_;
v_isShared_3508_ = v_isSharedCheck_3533_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_toSeqRight_3505_);
lean_inc(v_toSeqLeft_3504_);
lean_inc(v_toSeq_3503_);
lean_inc(v_toFunctor_3502_);
lean_dec(v_toApplicative_3498_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3533_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___f_3509_; lean_object* v___f_3510_; lean_object* v___f_3511_; lean_object* v___f_3512_; lean_object* v___x_3513_; lean_object* v___f_3514_; lean_object* v___f_3515_; lean_object* v___f_3516_; lean_object* v___x_3518_; 
v___f_3509_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3510_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3502_);
v___f_3511_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3511_, 0, v_toFunctor_3502_);
v___f_3512_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3512_, 0, v_toFunctor_3502_);
v___x_3513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3513_, 0, v___f_3511_);
lean_ctor_set(v___x_3513_, 1, v___f_3512_);
v___f_3514_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3514_, 0, v_toSeqRight_3505_);
v___f_3515_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3515_, 0, v_toSeqLeft_3504_);
v___f_3516_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3516_, 0, v_toSeq_3503_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 4, v___f_3514_);
lean_ctor_set(v___x_3507_, 3, v___f_3515_);
lean_ctor_set(v___x_3507_, 2, v___f_3516_);
lean_ctor_set(v___x_3507_, 1, v___f_3509_);
lean_ctor_set(v___x_3507_, 0, v___x_3513_);
v___x_3518_ = v___x_3507_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3513_);
lean_ctor_set(v_reuseFailAlloc_3532_, 1, v___f_3509_);
lean_ctor_set(v_reuseFailAlloc_3532_, 2, v___f_3516_);
lean_ctor_set(v_reuseFailAlloc_3532_, 3, v___f_3515_);
lean_ctor_set(v_reuseFailAlloc_3532_, 4, v___f_3514_);
v___x_3518_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
lean_object* v___x_3520_; 
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 1, v___f_3510_);
lean_ctor_set(v___x_3500_, 0, v___x_3518_);
v___x_3520_ = v___x_3500_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3518_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v___f_3510_);
v___x_3520_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v_toMonadRef_3523_; lean_object* v___f_3524_; lean_object* v___x_3525_; uint8_t v___x_3526_; lean_object* v___x_3527_; lean_object* v___f_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3521_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3);
v___x_3522_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7);
v_toMonadRef_3523_ = lean_ctor_get(v___x_3522_, 0);
v___f_3524_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__8));
v___x_3525_ = lean_unsigned_to_nat(0u);
v___x_3526_ = 0;
v___x_3527_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__9));
lean_inc_ref(v_toMonadRef_3523_);
v___f_3528_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_3528_, 0, v_probe_3480_);
lean_closure_set(v___f_3528_, 1, v___x_3527_);
lean_closure_set(v___f_3528_, 2, v_inst_3478_);
lean_closure_set(v___f_3528_, 3, v___x_3520_);
lean_closure_set(v___f_3528_, 4, v___x_3521_);
lean_closure_set(v___f_3528_, 5, v_toMonadRef_3523_);
lean_closure_set(v___f_3528_, 6, v___f_3524_);
v___x_3529_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__10));
v___x_3530_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3530_, 0, v___x_3525_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
lean_ctor_set(v___x_3530_, 2, v___f_3528_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3, v_phase_3479_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 1, v_phase_3479_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 2, v___x_3526_);
return v___x_3530_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___boxed(lean_object* v_inst_3537_, lean_object* v_phase_3538_, lean_object* v_probe_3539_){
_start:
{
uint8_t v_phase_boxed_3540_; lean_object* v_res_3541_; 
v_phase_boxed_3540_ = lean_unbox(v_phase_3538_);
v_res_3541_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg(v_inst_3537_, v_phase_boxed_3540_, v_probe_3539_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass(lean_object* v_00_u03b2_3542_, lean_object* v_inst_3543_, uint8_t v_phase_3544_, lean_object* v_probe_3545_){
_start:
{
lean_object* v___x_3546_; 
v___x_3546_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg(v_inst_3543_, v_phase_3544_, v_probe_3545_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___boxed(lean_object* v_00_u03b2_3547_, lean_object* v_inst_3548_, lean_object* v_phase_3549_, lean_object* v_probe_3550_){
_start:
{
uint8_t v_phase_boxed_3551_; lean_object* v_res_3552_; 
v_phase_boxed_3551_ = lean_unbox(v_phase_3549_);
v_res_3552_ = l_Lean_Compiler_LCNF_Probe_toPass(v_00_u03b2_3547_, v_inst_3548_, v_phase_boxed_3551_, v_probe_3550_);
return v_res_3552_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3611_ = lean_unsigned_to_nat(4008565020u);
v___x_3612_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3613_ = l_Lean_Name_num___override(v___x_3612_, v___x_3611_);
return v___x_3613_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3615_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3616_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3617_ = l_Lean_Name_str___override(v___x_3616_, v___x_3615_);
return v___x_3617_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3619_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3620_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3621_ = l_Lean_Name_str___override(v___x_3620_, v___x_3619_);
return v___x_3621_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v___x_3622_ = lean_unsigned_to_nat(2u);
v___x_3623_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3624_ = l_Lean_Name_num___override(v___x_3623_, v___x_3622_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3626_; uint8_t v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3626_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3627_ = 1;
v___x_3628_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3629_ = l_Lean_registerTraceClass(v___x_3626_, v___x_3627_, v___x_3628_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2____boxed(lean_object* v_a_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_();
return v_res_3631_;
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
