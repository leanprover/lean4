// Lean compiler output
// Module: Lean.Compiler.LCNF.PullFunDecls
// Imports: public import Lean.Compiler.LCNF.DependsOn public import Lean.Compiler.LCNF.PassManager
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFVarIdHashSet;
lean_object* l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1___redArg();
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDecl_collectUsed(uint8_t, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCode___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PullFunDecls_attach_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PullFunDecls_attach_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attach(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Compiler_LCNF_PullFunDecls_attachJps_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Compiler_LCNF_PullFunDecls_attachJps_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachJps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachJps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_addToPull(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_pull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullFunDecls_pull_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullFunDecls_pull_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_addToPull___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_pull___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Decl_pullFunDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_PullFunDecls_pull___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Decl_pullFunDecls___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_pullFunDecls___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullFunDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullFunDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_pullFunDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "pullFunDecls"};
static const lean_object* l_Lean_Compiler_LCNF_pullFunDecls___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_pullFunDecls___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_pullFunDecls___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_pullFunDecls___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 214, 187, 111, 27, 230, 209, 214)}};
static const lean_object* l_Lean_Compiler_LCNF_pullFunDecls___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_pullFunDecls___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_pullFunDecls___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Decl_pullFunDecls___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_pullFunDecls___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_pullFunDecls___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_pullFunDecls___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_pullFunDecls___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_pullFunDecls;
static const lean_string_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_pullFunDecls___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 137, 34, 178, 57, 97, 174, 106)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PullFunDecls"};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(34, 22, 167, 240, 97, 96, 111, 65)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(131, 100, 103, 236, 110, 190, 9, 116)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(78, 145, 55, 223, 32, 104, 111, 137)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(236, 31, 216, 154, 82, 114, 229, 5)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(173, 162, 66, 169, 209, 13, 217, 144)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(4, 162, 43, 226, 174, 157, 211, 6)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(141, 150, 70, 168, 50, 70, 196, 119)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 126, 218, 119, 38, 57, 70, 9)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 121, 99, 184, 127, 70, 201, 225)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(147, 165, 234, 171, 104, 161, 33, 84)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(136, 29, 219, 35, 181, 138, 226, 178)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1553090079) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(166, 206, 19, 9, 70, 7, 4, 159)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 149, 47, 183, 177, 167, 88, 77)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(89, 202, 79, 174, 233, 112, 55, 156)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(132, 9, 140, 163, 170, 173, 0, 118)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1___redArg();
return v___x_1_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; uint8_t v___x_4_; lean_object* v___x_5_; 
v___x_2_ = l_Lean_instInhabitedFVarIdHashSet;
v___x_3_ = lean_obj_once(&l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__0, &l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__0_once, _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__0);
v___x_4_ = 0;
v___x_5_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5_, 0, v___x_3_);
lean_ctor_set(v___x_5_, 1, v___x_2_);
lean_ctor_set_uint8(v___x_5_, sizeof(void*)*2, v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default(void){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_obj_once(&l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__1, &l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__1_once, _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__1);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default;
return v___x_7_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___redArg(lean_object* v_a_8_, lean_object* v_x_9_){
_start:
{
if (lean_obj_tag(v_x_9_) == 0)
{
uint8_t v___x_10_; 
v___x_10_ = 0;
return v___x_10_;
}
else
{
lean_object* v_key_11_; lean_object* v_tail_12_; uint8_t v___x_13_; 
v_key_11_ = lean_ctor_get(v_x_9_, 0);
v_tail_12_ = lean_ctor_get(v_x_9_, 2);
v___x_13_ = l_Lean_instBEqFVarId_beq(v_key_11_, v_a_8_);
if (v___x_13_ == 0)
{
v_x_9_ = v_tail_12_;
goto _start;
}
else
{
return v___x_13_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_8_ = stack[0].m_obj;
lean_object* v_x_9_ = stack[1].m_obj;
uint8_t v_res_15_;
v_res_15_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___redArg(v_a_8_, v_x_9_);
stack->m_num = v_res_15_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_16_, lean_object* v_x_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___redArg(v_a_16_, v_x_17_);
lean_dec(v_x_17_);
lean_dec(v_a_16_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(lean_object* v_m_20_, lean_object* v_a_21_){
_start:
{
lean_object* v_buckets_22_; lean_object* v___x_23_; uint64_t v___x_24_; uint64_t v___x_25_; uint64_t v___x_26_; uint64_t v_fold_27_; uint64_t v___x_28_; uint64_t v___x_29_; uint64_t v___x_30_; size_t v___x_31_; size_t v___x_32_; size_t v___x_33_; size_t v___x_34_; size_t v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v_buckets_22_ = lean_ctor_get(v_m_20_, 1);
v___x_23_ = lean_array_get_size(v_buckets_22_);
v___x_24_ = l_Lean_instHashableFVarId_hash(v_a_21_);
v___x_25_ = 32ULL;
v___x_26_ = lean_uint64_shift_right(v___x_24_, v___x_25_);
v_fold_27_ = lean_uint64_xor(v___x_24_, v___x_26_);
v___x_28_ = 16ULL;
v___x_29_ = lean_uint64_shift_right(v_fold_27_, v___x_28_);
v___x_30_ = lean_uint64_xor(v_fold_27_, v___x_29_);
v___x_31_ = lean_uint64_to_usize(v___x_30_);
v___x_32_ = lean_usize_of_nat(v___x_23_);
v___x_33_ = ((size_t)1ULL);
v___x_34_ = lean_usize_sub(v___x_32_, v___x_33_);
v___x_35_ = lean_usize_land(v___x_31_, v___x_34_);
v___x_36_ = lean_array_uget_borrowed(v_buckets_22_, v___x_35_);
v___x_37_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___redArg(v_a_21_, v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_20_ = stack[0].m_obj;
lean_object* v_a_21_ = stack[1].m_obj;
uint8_t v_res_38_;
v_res_38_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(v_m_20_, v_a_21_);
stack->m_num = v_res_38_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg___boxed(lean_object* v_m_39_, lean_object* v_a_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(v_m_39_, v_a_40_);
lean_dec(v_a_40_);
lean_dec_ref(v_m_39_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg(lean_object* v_fvarId_43_, lean_object* v_as_44_, lean_object* v_keep_45_, lean_object* v_dep_46_){
_start:
{
if (lean_obj_tag(v_as_44_) == 0)
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v_keep_45_);
lean_ctor_set(v___x_48_, 1, v_dep_46_);
v___x_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
return v___x_49_;
}
else
{
lean_object* v_head_50_; lean_object* v_tail_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_65_; 
v_head_50_ = lean_ctor_get(v_as_44_, 0);
v_tail_51_ = lean_ctor_get(v_as_44_, 1);
v_isSharedCheck_65_ = !lean_is_exclusive(v_as_44_);
if (v_isSharedCheck_65_ == 0)
{
v___x_53_ = v_as_44_;
v_isShared_54_ = v_isSharedCheck_65_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_tail_51_);
lean_inc(v_head_50_);
lean_dec(v_as_44_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_65_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v_used_55_; uint8_t v___x_56_; 
v_used_55_ = lean_ctor_get(v_head_50_, 1);
v___x_56_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(v_used_55_, v_fvarId_43_);
if (v___x_56_ == 0)
{
lean_object* v___x_58_; 
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 1, v_keep_45_);
v___x_58_ = v___x_53_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_head_50_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_keep_45_);
v___x_58_ = v_reuseFailAlloc_60_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
v_as_44_ = v_tail_51_;
v_keep_45_ = v___x_58_;
goto _start;
}
}
else
{
lean_object* v___x_62_; 
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 1, v_dep_46_);
v___x_62_ = v___x_53_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_head_50_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_dep_46_);
v___x_62_ = v_reuseFailAlloc_64_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
v_as_44_ = v_tail_51_;
v_dep_46_ = v___x_62_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_43_ = stack[0].m_obj;
lean_object* v_as_44_ = stack[1].m_obj;
lean_object* v_keep_45_ = stack[2].m_obj;
lean_object* v_dep_46_ = stack[3].m_obj;
lean_object* v_res_66_;
v_res_66_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg(v_fvarId_43_, v_as_44_, v_keep_45_, v_dep_46_);
stack->m_obj
 = v_res_66_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg___boxed(lean_object* v_fvarId_67_, lean_object* v_as_68_, lean_object* v_keep_69_, lean_object* v_dep_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg(v_fvarId_67_, v_as_68_, v_keep_69_, v_dep_70_);
lean_dec(v_fvarId_67_);
return v_res_72_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go(lean_object* v_fvarId_73_, lean_object* v_as_74_, lean_object* v_keep_75_, lean_object* v_dep_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg(v_fvarId_73_, v_as_74_, v_keep_75_, v_dep_76_);
return v___x_80_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_73_ = stack[0].m_obj;
lean_object* v_as_74_ = stack[1].m_obj;
lean_object* v_keep_75_ = stack[2].m_obj;
lean_object* v_dep_76_ = stack[3].m_obj;
lean_object* v_a_77_ = stack[4].m_obj;
lean_object* v_a_78_ = stack[5].m_obj;
lean_object* v_res_81_;
v_res_81_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go(v_fvarId_73_, v_as_74_, v_keep_75_, v_dep_76_, v_a_77_, v_a_78_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___boxed(lean_object* v_fvarId_82_, lean_object* v_as_83_, lean_object* v_keep_84_, lean_object* v_dep_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go(v_fvarId_82_, v_as_83_, v_keep_84_, v_dep_85_, v_a_86_, v_a_87_);
lean_dec(v_a_87_);
lean_dec_ref(v_a_86_);
lean_dec(v_fvarId_82_);
return v_res_89_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0(lean_object* v_00_u03b2_90_, lean_object* v_m_91_, lean_object* v_a_92_){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(v_m_91_, v_a_92_);
return v___x_93_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_91_ = stack[1].m_obj;
lean_object* v_a_92_ = stack[2].m_obj;
uint8_t v_res_94_;
v_res_94_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0(lean_box(0), v_m_91_, v_a_92_);
stack->m_num = v_res_94_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___boxed(lean_object* v_00_u03b2_95_, lean_object* v_m_96_, lean_object* v_a_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0(v_00_u03b2_95_, v_m_96_, v_a_97_);
lean_dec(v_a_97_);
lean_dec_ref(v_m_96_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0(lean_object* v_00_u03b2_100_, lean_object* v_a_101_, lean_object* v_x_102_){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___redArg(v_a_101_, v_x_102_);
return v___x_103_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_101_ = stack[1].m_obj;
lean_object* v_x_102_ = stack[2].m_obj;
uint8_t v_res_104_;
v_res_104_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0(lean_box(0), v_a_101_, v_x_102_);
stack->m_num = v_res_104_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_105_, lean_object* v_a_106_, lean_object* v_x_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0(v_00_u03b2_105_, v_a_106_, v_x_107_);
lean_dec(v_x_107_);
lean_dec(v_a_106_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
uint8_t l_List_any___at___00Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_spec__0(lean_object* v_fvarId_110_, lean_object* v_x_111_){
_start:
{
if (lean_obj_tag(v_x_111_) == 0)
{
uint8_t v___x_112_; 
v___x_112_ = 0;
return v___x_112_;
}
else
{
lean_object* v_head_113_; lean_object* v_tail_114_; lean_object* v_used_115_; uint8_t v___x_116_; 
v_head_113_ = lean_ctor_get(v_x_111_, 0);
v_tail_114_ = lean_ctor_get(v_x_111_, 1);
v_used_115_ = lean_ctor_get(v_head_113_, 1);
v___x_116_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(v_used_115_, v_fvarId_110_);
if (v___x_116_ == 0)
{
v_x_111_ = v_tail_114_;
goto _start;
}
else
{
return v___x_116_;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_110_ = stack[0].m_obj;
lean_object* v_x_111_ = stack[1].m_obj;
uint8_t v_res_118_;
v_res_118_ = l_List_any___at___00Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_spec__0(v_fvarId_110_, v_x_111_);
stack->m_num = v_res_118_;
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_spec__0___boxed(lean_object* v_fvarId_119_, lean_object* v_x_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_List_any___at___00Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_spec__0(v_fvarId_119_, v_x_120_);
lean_dec(v_x_120_);
lean_dec(v_fvarId_119_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(lean_object* v_fvarId_123_, lean_object* v_a_124_){
_start:
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_st_ref_get(v_a_124_);
v___x_127_ = l_List_any___at___00Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_spec__0(v_fvarId_123_, v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec(v___x_126_);
v___x_128_ = lean_box(0);
v___x_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_142_; 
v___x_130_ = lean_box(0);
v___x_131_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg(v_fvarId_123_, v___x_126_, v___x_130_, v___x_130_);
v_a_132_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_142_ == 0)
{
v___x_134_ = v___x_131_;
v_isShared_135_ = v_isSharedCheck_142_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_131_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_142_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v_fst_136_; lean_object* v_snd_137_; lean_object* v___x_138_; lean_object* v___x_140_; 
v_fst_136_ = lean_ctor_get(v_a_132_, 0);
lean_inc(v_fst_136_);
v_snd_137_ = lean_ctor_get(v_a_132_, 1);
lean_inc(v_snd_137_);
lean_dec(v_a_132_);
v___x_138_ = lean_st_ref_swap(v_a_124_, v_fst_136_);
lean_dec(v___x_138_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v_snd_137_);
v___x_140_ = v___x_134_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_snd_137_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_123_ = stack[0].m_obj;
lean_object* v_a_124_ = stack[1].m_obj;
lean_object* v_res_143_;
v_res_143_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(v_fvarId_123_, v_a_124_);
stack->m_obj
 = v_res_143_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg___boxed(lean_object* v_fvarId_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(v_fvarId_144_, v_a_145_);
lean_dec(v_a_145_);
lean_dec(v_fvarId_144_);
return v_res_147_;
}
}
lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps(lean_object* v_fvarId_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(v_fvarId_148_, v_a_149_);
return v___x_155_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_148_ = stack[0].m_obj;
lean_object* v_a_149_ = stack[1].m_obj;
lean_object* v_a_150_ = stack[2].m_obj;
lean_object* v_a_151_ = stack[3].m_obj;
lean_object* v_a_152_ = stack[4].m_obj;
lean_object* v_a_153_ = stack[5].m_obj;
lean_object* v_res_156_;
v_res_156_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps(v_fvarId_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
stack->m_obj
 = v_res_156_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___boxed(lean_object* v_fvarId_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps(v_fvarId_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec(v_fvarId_157_);
return v_res_164_;
}
}
lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(lean_object* v_todo_165_, lean_object* v_acc_166_, lean_object* v_a_167_){
_start:
{
if (lean_obj_tag(v_todo_165_) == 0)
{
lean_object* v___x_169_; 
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v_acc_166_);
return v___x_169_;
}
else
{
lean_object* v_head_170_; lean_object* v_decl_171_; lean_object* v_tail_172_; lean_object* v_fvarId_173_; lean_object* v___x_174_; 
v_head_170_ = lean_ctor_get(v_todo_165_, 0);
lean_inc(v_head_170_);
v_decl_171_ = lean_ctor_get(v_head_170_, 0);
v_tail_172_ = lean_ctor_get(v_todo_165_, 1);
lean_inc(v_tail_172_);
lean_dec_ref_known(v_todo_165_, 2);
v_fvarId_173_ = lean_ctor_get(v_decl_171_, 0);
v___x_174_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(v_fvarId_173_, v_a_167_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_a_175_);
lean_dec_ref_known(v___x_174_, 1);
v___x_176_ = l_List_appendTR___redArg(v_a_175_, v_tail_172_);
v___x_177_ = lean_array_push(v_acc_166_, v_head_170_);
v_todo_165_ = v___x_176_;
v_acc_166_ = v___x_177_;
goto _start;
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
lean_dec(v_tail_172_);
lean_dec(v_head_170_);
lean_dec_ref(v_acc_166_);
v_a_179_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_174_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_174_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_todo_165_ = stack[0].m_obj;
lean_object* v_acc_166_ = stack[1].m_obj;
lean_object* v_a_167_ = stack[2].m_obj;
lean_object* v_res_187_;
v_res_187_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(v_todo_165_, v_acc_166_, v_a_167_);
stack->m_obj
 = v_res_187_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg___boxed(lean_object* v_todo_188_, lean_object* v_acc_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(v_todo_188_, v_acc_189_, v_a_190_);
lean_dec(v_a_190_);
return v_res_192_;
}
}
lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint(lean_object* v_todo_193_, lean_object* v_acc_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(v_todo_193_, v_acc_194_, v_a_195_);
return v___x_201_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint_0interp(lean_interpreter_value* stack)
{
lean_object* v_todo_193_ = stack[0].m_obj;
lean_object* v_acc_194_ = stack[1].m_obj;
lean_object* v_a_195_ = stack[2].m_obj;
lean_object* v_a_196_ = stack[3].m_obj;
lean_object* v_a_197_ = stack[4].m_obj;
lean_object* v_a_198_ = stack[5].m_obj;
lean_object* v_a_199_ = stack[6].m_obj;
lean_object* v_res_202_;
v_res_202_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint(v_todo_193_, v_acc_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_);
stack->m_obj
 = v_res_202_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___boxed(lean_object* v_todo_203_, lean_object* v_acc_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint(v_todo_203_, v_acc_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
return v_res_211_;
}
}
lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(lean_object* v_fvarId_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(v_fvarId_214_, v_a_215_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_a_218_);
lean_dec_ref_known(v___x_217_, 1);
v___x_219_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___closed__0));
v___x_220_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(v_a_218_, v___x_219_, v_a_215_);
return v___x_220_;
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
v_a_221_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_217_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_217_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_214_ = stack[0].m_obj;
lean_object* v_a_215_ = stack[1].m_obj;
lean_object* v_res_229_;
v_res_229_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(v_fvarId_214_, v_a_215_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___boxed(lean_object* v_fvarId_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(v_fvarId_230_, v_a_231_);
lean_dec(v_a_231_);
lean_dec(v_fvarId_230_);
return v_res_233_;
}
}
lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps(lean_object* v_fvarId_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(v_fvarId_234_, v_a_235_);
return v___x_241_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_234_ = stack[0].m_obj;
lean_object* v_a_235_ = stack[1].m_obj;
lean_object* v_a_236_ = stack[2].m_obj;
lean_object* v_a_237_ = stack[3].m_obj;
lean_object* v_a_238_ = stack[4].m_obj;
lean_object* v_a_239_ = stack[5].m_obj;
lean_object* v_res_242_;
v_res_242_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps(v_fvarId_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_);
stack->m_obj
 = v_res_242_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___boxed(lean_object* v_fvarId_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps(v_fvarId_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec(v_fvarId_243_);
return v_res_250_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg(lean_object* v_as_251_, size_t v_sz_252_, size_t v_i_253_, lean_object* v_b_254_, lean_object* v___y_255_){
_start:
{
uint8_t v___x_257_; 
v___x_257_ = lean_usize_dec_lt(v_i_253_, v_sz_252_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v_b_254_);
return v___x_258_;
}
else
{
lean_object* v_a_259_; lean_object* v_fvarId_260_; lean_object* v___x_261_; 
v_a_259_ = lean_array_uget_borrowed(v_as_251_, v_i_253_);
v_fvarId_260_ = lean_ctor_get(v_a_259_, 0);
v___x_261_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(v_fvarId_260_, v___y_255_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_263_; size_t v___x_264_; size_t v___x_265_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v___x_261_, 1);
v___x_263_ = l_Array_append___redArg(v_b_254_, v_a_262_);
lean_dec(v_a_262_);
v___x_264_ = ((size_t)1ULL);
v___x_265_ = lean_usize_add(v_i_253_, v___x_264_);
v_i_253_ = v___x_265_;
v_b_254_ = v___x_263_;
goto _start;
}
else
{
lean_dec_ref(v_b_254_);
return v___x_261_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_251_ = stack[0].m_obj;
size_t v_sz_252_ = stack[1].m_num;
size_t v_i_253_ = stack[2].m_num;
lean_object* v_b_254_ = stack[3].m_obj;
lean_object* v___y_255_ = stack[4].m_obj;
lean_object* v_res_267_;
v_res_267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg(v_as_251_, v_sz_252_, v_i_253_, v_b_254_, v___y_255_);
stack->m_obj
 = v_res_267_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg___boxed(lean_object* v_as_268_, lean_object* v_sz_269_, lean_object* v_i_270_, lean_object* v_b_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
size_t v_sz_boxed_274_; size_t v_i_boxed_275_; lean_object* v_res_276_; 
v_sz_boxed_274_ = lean_unbox_usize(v_sz_269_);
lean_dec(v_sz_269_);
v_i_boxed_275_ = lean_unbox_usize(v_i_270_);
lean_dec(v_i_270_);
v_res_276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg(v_as_268_, v_sz_boxed_274_, v_i_boxed_275_, v_b_271_, v___y_272_);
lean_dec(v___y_272_);
lean_dec_ref(v_as_268_);
return v_res_276_;
}
}
lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg(lean_object* v_params_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_acc_284_; size_t v_sz_285_; size_t v___x_286_; lean_object* v___x_287_; 
v_acc_284_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___closed__0));
v_sz_285_ = lean_array_size(v_params_277_);
v___x_286_ = ((size_t)0ULL);
v___x_287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg(v_params_277_, v_sz_285_, v___x_286_, v_acc_284_, v_a_278_);
return v___x_287_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_277_ = stack[0].m_obj;
lean_object* v_a_278_ = stack[1].m_obj;
lean_object* v_a_279_ = stack[2].m_obj;
lean_object* v_a_280_ = stack[3].m_obj;
lean_object* v_a_281_ = stack[4].m_obj;
lean_object* v_a_282_ = stack[5].m_obj;
lean_object* v_res_288_;
v_res_288_ = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg(v_params_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_);
stack->m_obj
 = v_res_288_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg___boxed(lean_object* v_params_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg(v_params_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_a_290_);
lean_dec_ref(v_params_289_);
return v_res_296_;
}
}
lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps(uint8_t v_pu_297_, lean_object* v_params_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg(v_params_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
return v___x_305_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_297_ = stack[0].m_num;
lean_object* v_params_298_ = stack[1].m_obj;
lean_object* v_a_299_ = stack[2].m_obj;
lean_object* v_a_300_ = stack[3].m_obj;
lean_object* v_a_301_ = stack[4].m_obj;
lean_object* v_a_302_ = stack[5].m_obj;
lean_object* v_a_303_ = stack[6].m_obj;
lean_object* v_res_306_;
v_res_306_ = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps(v_pu_297_, v_params_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
stack->m_obj
 = v_res_306_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___boxed(lean_object* v_pu_307_, lean_object* v_params_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
uint8_t v_pu_boxed_315_; lean_object* v_res_316_; 
v_pu_boxed_315_ = lean_unbox(v_pu_307_);
v_res_316_ = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps(v_pu_boxed_315_, v_params_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_params_308_);
return v_res_316_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0(lean_object* v_as_317_, size_t v_sz_318_, size_t v_i_319_, lean_object* v_b_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg(v_as_317_, v_sz_318_, v_i_319_, v_b_320_, v___y_321_);
return v___x_327_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_317_ = stack[0].m_obj;
size_t v_sz_318_ = stack[1].m_num;
size_t v_i_319_ = stack[2].m_num;
lean_object* v_b_320_ = stack[3].m_obj;
lean_object* v___y_321_ = stack[4].m_obj;
lean_object* v___y_322_ = stack[5].m_obj;
lean_object* v___y_323_ = stack[6].m_obj;
lean_object* v___y_324_ = stack[7].m_obj;
lean_object* v___y_325_ = stack[8].m_obj;
lean_object* v_res_328_;
v_res_328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0(v_as_317_, v_sz_318_, v_i_319_, v_b_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
stack->m_obj
 = v_res_328_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___boxed(lean_object* v_as_329_, lean_object* v_sz_330_, lean_object* v_i_331_, lean_object* v_b_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
size_t v_sz_boxed_339_; size_t v_i_boxed_340_; lean_object* v_res_341_; 
v_sz_boxed_339_ = lean_unbox_usize(v_sz_330_);
lean_dec(v_sz_330_);
v_i_boxed_340_ = lean_unbox_usize(v_i_331_);
lean_dec(v_i_331_);
v_res_341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0(v_as_329_, v_sz_boxed_339_, v_i_boxed_340_, v_b_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v_as_329_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach(lean_object* v_p_342_, lean_object* v_k_343_){
_start:
{
uint8_t v_isFun_344_; 
v_isFun_344_ = lean_ctor_get_uint8(v_p_342_, sizeof(void*)*2);
if (v_isFun_344_ == 0)
{
lean_object* v_decl_345_; lean_object* v___x_346_; 
v_decl_345_ = lean_ctor_get(v_p_342_, 0);
lean_inc_ref(v_decl_345_);
v___x_346_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_346_, 0, v_decl_345_);
lean_ctor_set(v___x_346_, 1, v_k_343_);
return v___x_346_;
}
else
{
lean_object* v_decl_347_; lean_object* v___x_348_; 
v_decl_347_ = lean_ctor_get(v_p_342_, 0);
lean_inc_ref(v_decl_347_);
v___x_348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_348_, 0, v_decl_347_);
lean_ctor_set(v___x_348_, 1, v_k_343_);
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach___boxed(lean_object* v_p_349_, lean_object* v_k_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach(v_p_349_, v_k_350_);
lean_dec_ref(v_p_349_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited(lean_object* v_i_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_snd_354_; uint8_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_snd_354_ = lean_ctor_get(v_a_353_, 1);
v___x_355_ = 0;
v___x_356_ = lean_box(v___x_355_);
v___x_357_ = lean_array_get(v___x_356_, v_snd_354_, v_i_352_);
lean_dec(v___x_356_);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v_a_353_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited___boxed(lean_object* v_i_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited(v_i_359_, v_a_360_);
lean_dec(v_i_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg(lean_object* v_upperBound_362_, lean_object* v___x_363_, lean_object* v_ps_364_, lean_object* v_a_365_, lean_object* v_b_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_a_369_; lean_object* v_snd_370_; uint8_t v___x_374_; 
v___x_374_ = lean_nat_dec_lt(v_a_365_, v_upperBound_362_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; 
lean_dec(v_a_365_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v_b_366_);
lean_ctor_set(v___x_375_, 1, v___y_367_);
return v___x_375_;
}
else
{
lean_object* v___x_376_; lean_object* v_fst_377_; lean_object* v_snd_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_376_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited(v_a_365_, v___y_367_);
v_fst_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_fst_377_);
v_snd_378_ = lean_ctor_get(v___x_376_, 1);
lean_inc(v_snd_378_);
lean_dec_ref(v___x_376_);
v___x_379_ = lean_box(0);
v___x_380_ = lean_unbox(v_fst_377_);
lean_dec(v_fst_377_);
if (v___x_380_ == 0)
{
lean_object* v_decl_381_; lean_object* v_fvarId_382_; lean_object* v___x_383_; lean_object* v_used_384_; uint8_t v___x_385_; 
v_decl_381_ = lean_ctor_get(v___x_363_, 0);
v_fvarId_382_ = lean_ctor_get(v_decl_381_, 0);
v___x_383_ = lean_array_fget_borrowed(v_ps_364_, v_a_365_);
v_used_384_ = lean_ctor_get(v___x_383_, 1);
v___x_385_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(v_used_384_, v_fvarId_382_);
if (v___x_385_ == 0)
{
v_a_369_ = v___x_379_;
v_snd_370_ = v_snd_378_;
goto v___jp_368_;
}
else
{
lean_object* v___x_386_; lean_object* v_snd_387_; 
v___x_386_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit(v_ps_364_, v_a_365_, v_snd_378_);
v_snd_387_ = lean_ctor_get(v___x_386_, 1);
lean_inc(v_snd_387_);
lean_dec_ref(v___x_386_);
v_a_369_ = v___x_379_;
v_snd_370_ = v_snd_387_;
goto v___jp_368_;
}
}
else
{
v_a_369_ = v___x_379_;
v_snd_370_ = v_snd_378_;
goto v___jp_368_;
}
}
v___jp_368_:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_nat_add(v_a_365_, v___x_371_);
lean_dec(v_a_365_);
v_a_365_ = v___x_372_;
v_b_366_ = v_a_369_;
v___y_367_ = v_snd_370_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit(lean_object* v_ps_388_, lean_object* v_i_389_, lean_object* v_a_390_){
_start:
{
lean_object* v___x_391_; lean_object* v_fst_392_; uint8_t v___x_393_; 
v___x_391_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited(v_i_389_, v_a_390_);
v_fst_392_ = lean_ctor_get(v___x_391_, 0);
v___x_393_ = lean_unbox(v_fst_392_);
if (v___x_393_ == 0)
{
lean_object* v_snd_394_; lean_object* v_fst_395_; lean_object* v_snd_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_431_; 
v_snd_394_ = lean_ctor_get(v___x_391_, 1);
lean_inc(v_snd_394_);
lean_dec_ref(v___x_391_);
v_fst_395_ = lean_ctor_get(v_snd_394_, 0);
v_snd_396_ = lean_ctor_get(v_snd_394_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v_snd_394_);
if (v_isSharedCheck_431_ == 0)
{
v___x_398_ = v_snd_394_;
v_isShared_399_ = v_isSharedCheck_431_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_snd_396_);
lean_inc(v_fst_395_);
lean_dec(v_snd_394_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_431_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_400_ = l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default;
v___x_401_ = lean_array_get_size(v_ps_388_);
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = 1;
v___x_404_ = lean_box(v___x_403_);
v___x_405_ = lean_array_set(v_snd_396_, v_i_389_, v___x_404_);
v___x_406_ = lean_array_get_borrowed(v___x_400_, v_ps_388_, v_i_389_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 1, v___x_405_);
v___x_408_ = v___x_398_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_fst_395_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v___x_405_);
v___x_408_ = v_reuseFailAlloc_430_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v_snd_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_428_; 
v___x_409_ = lean_box(0);
v___x_410_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg(v___x_401_, v___x_406_, v_ps_388_, v___x_402_, v___x_409_, v___x_408_);
v_snd_411_ = lean_ctor_get(v___x_410_, 1);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_428_ == 0)
{
lean_object* v_unused_429_; 
v_unused_429_ = lean_ctor_get(v___x_410_, 0);
lean_dec(v_unused_429_);
v___x_413_ = v___x_410_;
v_isShared_414_ = v_isSharedCheck_428_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_snd_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_428_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v_fst_415_; lean_object* v_snd_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_427_; 
v_fst_415_ = lean_ctor_get(v_snd_411_, 0);
v_snd_416_ = lean_ctor_get(v_snd_411_, 1);
v_isSharedCheck_427_ = !lean_is_exclusive(v_snd_411_);
if (v_isSharedCheck_427_ == 0)
{
v___x_418_ = v_snd_411_;
v_isShared_419_ = v_isSharedCheck_427_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_snd_416_);
lean_inc(v_fst_415_);
lean_dec(v_snd_411_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_427_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_420_ = l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach(v___x_406_, v_fst_415_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_420_);
v___x_422_ = v___x_418_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_snd_416_);
v___x_422_ = v_reuseFailAlloc_426_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_424_; 
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v___x_422_);
lean_ctor_set(v___x_413_, 0, v___x_409_);
v___x_424_ = v___x_413_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
}
}
else
{
lean_object* v_snd_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_440_; 
v_snd_432_ = lean_ctor_get(v___x_391_, 1);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; 
v_unused_441_ = lean_ctor_get(v___x_391_, 0);
lean_dec(v_unused_441_);
v___x_434_ = v___x_391_;
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_snd_432_);
lean_dec(v___x_391_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = lean_box(0);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_436_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_snd_432_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit___boxed(lean_object* v_ps_442_, lean_object* v_i_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit(v_ps_442_, v_i_443_, v_a_444_);
lean_dec(v_i_443_);
lean_dec_ref(v_ps_442_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg___boxed(lean_object* v_upperBound_446_, lean_object* v___x_447_, lean_object* v_ps_448_, lean_object* v_a_449_, lean_object* v_b_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg(v_upperBound_446_, v___x_447_, v_ps_448_, v_a_449_, v_b_450_, v___y_451_);
lean_dec_ref(v_ps_448_);
lean_dec_ref(v___x_447_);
lean_dec(v_upperBound_446_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0(lean_object* v_upperBound_453_, lean_object* v___x_454_, lean_object* v_ps_455_, lean_object* v_inst_456_, lean_object* v_R_457_, lean_object* v_a_458_, lean_object* v_b_459_, lean_object* v_c_460_, lean_object* v___y_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg(v_upperBound_453_, v___x_454_, v_ps_455_, v_a_458_, v_b_459_, v___y_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___boxed(lean_object* v_upperBound_463_, lean_object* v___x_464_, lean_object* v_ps_465_, lean_object* v_inst_466_, lean_object* v_R_467_, lean_object* v_a_468_, lean_object* v_b_469_, lean_object* v_c_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0(v_upperBound_463_, v___x_464_, v_ps_465_, v_inst_466_, v_R_467_, v_a_468_, v_b_469_, v_c_470_, v___y_471_);
lean_dec_ref(v_ps_465_);
lean_dec_ref(v___x_464_);
lean_dec(v_upperBound_463_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg(lean_object* v_upperBound_473_, lean_object* v_ps_474_, lean_object* v_a_475_, lean_object* v_b_476_, lean_object* v___y_477_){
_start:
{
uint8_t v___x_478_; 
v___x_478_ = lean_nat_dec_lt(v_a_475_, v_upperBound_473_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
lean_dec(v_a_475_);
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v_b_476_);
lean_ctor_set(v___x_479_, 1, v___y_477_);
return v___x_479_;
}
else
{
lean_object* v___x_480_; lean_object* v_snd_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_480_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit(v_ps_474_, v_a_475_, v___y_477_);
v_snd_481_ = lean_ctor_get(v___x_480_, 1);
lean_inc(v_snd_481_);
lean_dec_ref(v___x_480_);
v___x_482_ = lean_box(0);
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = lean_nat_add(v_a_475_, v___x_483_);
lean_dec(v_a_475_);
v_a_475_ = v___x_484_;
v_b_476_ = v___x_482_;
v___y_477_ = v_snd_481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg___boxed(lean_object* v_upperBound_486_, lean_object* v_ps_487_, lean_object* v_a_488_, lean_object* v_b_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg(v_upperBound_486_, v_ps_487_, v_a_488_, v_b_489_, v___y_490_);
lean_dec_ref(v_ps_487_);
lean_dec(v_upperBound_486_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go(lean_object* v_ps_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v_snd_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
v___x_494_ = lean_array_get_size(v_ps_492_);
v___x_495_ = lean_unsigned_to_nat(0u);
v___x_496_ = lean_box(0);
v___x_497_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg(v___x_494_, v_ps_492_, v___x_495_, v___x_496_, v_a_493_);
v_snd_498_ = lean_ctor_get(v___x_497_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v___x_497_, 0);
lean_dec(v_unused_506_);
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_snd_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_496_);
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_snd_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go___boxed(lean_object* v_ps_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go(v_ps_507_, v_a_508_);
lean_dec_ref(v_ps_507_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0(lean_object* v_upperBound_510_, lean_object* v_ps_511_, lean_object* v_inst_512_, lean_object* v_R_513_, lean_object* v_a_514_, lean_object* v_b_515_, lean_object* v_c_516_, lean_object* v___y_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg(v_upperBound_510_, v_ps_511_, v_a_514_, v_b_515_, v___y_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___boxed(lean_object* v_upperBound_519_, lean_object* v_ps_520_, lean_object* v_inst_521_, lean_object* v_R_522_, lean_object* v_a_523_, lean_object* v_b_524_, lean_object* v_c_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0(v_upperBound_519_, v_ps_520_, v_inst_521_, v_R_522_, v_a_523_, v_b_524_, v_c_525_, v___y_526_);
lean_dec_ref(v_ps_520_);
lean_dec(v_upperBound_519_);
return v_res_527_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PullFunDecls_attach_spec__0(size_t v_sz_528_, size_t v_i_529_, lean_object* v_bs_530_){
_start:
{
uint8_t v___x_531_; 
v___x_531_ = lean_usize_dec_lt(v_i_529_, v_sz_528_);
if (v___x_531_ == 0)
{
return v_bs_530_;
}
else
{
lean_object* v___x_532_; lean_object* v_bs_x27_533_; uint8_t v___x_534_; size_t v___x_535_; size_t v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_532_ = lean_unsigned_to_nat(0u);
v_bs_x27_533_ = lean_array_uset(v_bs_530_, v_i_529_, v___x_532_);
v___x_534_ = 0;
v___x_535_ = ((size_t)1ULL);
v___x_536_ = lean_usize_add(v_i_529_, v___x_535_);
v___x_537_ = lean_box(v___x_534_);
v___x_538_ = lean_array_uset(v_bs_x27_533_, v_i_529_, v___x_537_);
v_i_529_ = v___x_536_;
v_bs_530_ = v___x_538_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PullFunDecls_attach_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_528_ = stack[0].m_num;
size_t v_i_529_ = stack[1].m_num;
lean_object* v_bs_530_ = stack[2].m_obj;
lean_object* v_res_540_;
v_res_540_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PullFunDecls_attach_spec__0(v_sz_528_, v_i_529_, v_bs_530_);
stack->m_obj
 = v_res_540_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PullFunDecls_attach_spec__0___boxed(lean_object* v_sz_541_, lean_object* v_i_542_, lean_object* v_bs_543_){
_start:
{
size_t v_sz_boxed_544_; size_t v_i_boxed_545_; lean_object* v_res_546_; 
v_sz_boxed_544_ = lean_unbox_usize(v_sz_541_);
lean_dec(v_sz_541_);
v_i_boxed_545_ = lean_unbox_usize(v_i_542_);
lean_dec(v_i_542_);
v_res_546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PullFunDecls_attach_spec__0(v_sz_boxed_544_, v_i_boxed_545_, v_bs_543_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attach(lean_object* v_ps_547_, lean_object* v_k_548_){
_start:
{
size_t v_sz_549_; size_t v___x_550_; lean_object* v_visited_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v_snd_554_; lean_object* v_fst_555_; 
v_sz_549_ = lean_array_size(v_ps_547_);
v___x_550_ = ((size_t)0ULL);
lean_inc_ref(v_ps_547_);
v_visited_551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PullFunDecls_attach_spec__0(v_sz_549_, v___x_550_, v_ps_547_);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v_k_548_);
lean_ctor_set(v___x_552_, 1, v_visited_551_);
v___x_553_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go(v_ps_547_, v___x_552_);
lean_dec_ref(v_ps_547_);
v_snd_554_ = lean_ctor_get(v___x_553_, 1);
lean_inc(v_snd_554_);
lean_dec_ref(v___x_553_);
v_fst_555_ = lean_ctor_get(v_snd_554_, 0);
lean_inc(v_fst_555_);
lean_dec(v_snd_554_);
return v_fst_555_;
}
}
lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg(lean_object* v_fvarId_556_, lean_object* v_k_557_, lean_object* v_a_558_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(v_fvarId_556_, v_a_558_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_569_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_569_ == 0)
{
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_569_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_569_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_565_ = l_Lean_Compiler_LCNF_PullFunDecls_attach(v_a_561_, v_k_557_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_565_);
v___x_567_ = v___x_563_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_dec_ref(v_k_557_);
v_a_570_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_560_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_560_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_556_ = stack[0].m_obj;
lean_object* v_k_557_ = stack[1].m_obj;
lean_object* v_a_558_ = stack[2].m_obj;
lean_object* v_res_578_;
v_res_578_ = l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg(v_fvarId_556_, v_k_557_, v_a_558_);
stack->m_obj
 = v_res_578_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg___boxed(lean_object* v_fvarId_579_, lean_object* v_k_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg(v_fvarId_579_, v_k_580_, v_a_581_);
lean_dec(v_a_581_);
lean_dec(v_fvarId_579_);
return v_res_583_;
}
}
lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps(lean_object* v_fvarId_584_, lean_object* v_k_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg(v_fvarId_584_, v_k_585_, v_a_586_);
return v___x_592_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_584_ = stack[0].m_obj;
lean_object* v_k_585_ = stack[1].m_obj;
lean_object* v_a_586_ = stack[2].m_obj;
lean_object* v_a_587_ = stack[3].m_obj;
lean_object* v_a_588_ = stack[4].m_obj;
lean_object* v_a_589_ = stack[5].m_obj;
lean_object* v_a_590_ = stack[6].m_obj;
lean_object* v_res_593_;
v_res_593_ = l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps(v_fvarId_584_, v_k_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
stack->m_obj
 = v_res_593_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___boxed(lean_object* v_fvarId_594_, lean_object* v_k_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps(v_fvarId_594_, v_k_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec(v_a_596_);
lean_dec(v_fvarId_594_);
return v_res_602_;
}
}
lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(lean_object* v_params_603_, lean_object* v_k_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg(v_params_603_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_620_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_620_ == 0)
{
v___x_614_ = v___x_611_;
v_isShared_615_ = v_isSharedCheck_620_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_611_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_620_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_616_ = l_Lean_Compiler_LCNF_PullFunDecls_attach(v_a_612_, v_k_604_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_616_);
v___x_618_ = v___x_614_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v_k_604_);
v_a_621_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_611_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_611_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_603_ = stack[0].m_obj;
lean_object* v_k_604_ = stack[1].m_obj;
lean_object* v_a_605_ = stack[2].m_obj;
lean_object* v_a_606_ = stack[3].m_obj;
lean_object* v_a_607_ = stack[4].m_obj;
lean_object* v_a_608_ = stack[5].m_obj;
lean_object* v_a_609_ = stack[6].m_obj;
lean_object* v_res_629_;
v_res_629_ = l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(v_params_603_, v_k_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
stack->m_obj
 = v_res_629_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps___boxed(lean_object* v_params_630_, lean_object* v_k_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(v_params_630_, v_k_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec(v_a_632_);
lean_dec_ref(v_params_630_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Compiler_LCNF_PullFunDecls_attachJps_spec__1(lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
if (lean_obj_tag(v_a_639_) == 0)
{
lean_object* v___x_641_; 
v___x_641_ = l_List_reverse___redArg(v_a_640_);
return v___x_641_;
}
else
{
lean_object* v_head_642_; uint8_t v_isFun_643_; 
v_head_642_ = lean_ctor_get(v_a_639_, 0);
v_isFun_643_ = lean_ctor_get_uint8(v_head_642_, sizeof(void*)*2);
if (v_isFun_643_ == 0)
{
lean_object* v_tail_644_; 
v_tail_644_ = lean_ctor_get(v_a_639_, 1);
lean_inc(v_tail_644_);
lean_dec_ref_known(v_a_639_, 2);
v_a_639_ = v_tail_644_;
goto _start;
}
else
{
lean_object* v_tail_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_654_; 
lean_inc(v_head_642_);
v_tail_646_ = lean_ctor_get(v_a_639_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_a_639_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; 
v_unused_655_ = lean_ctor_get(v_a_639_, 0);
lean_dec(v_unused_655_);
v___x_648_ = v_a_639_;
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_tail_646_);
lean_dec(v_a_639_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v_a_640_);
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_head_642_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_a_640_);
v___x_651_ = v_reuseFailAlloc_653_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
v_a_639_ = v_tail_646_;
v_a_640_ = v___x_651_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Compiler_LCNF_PullFunDecls_attachJps_spec__0(lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
if (lean_obj_tag(v_a_656_) == 0)
{
lean_object* v___x_658_; 
v___x_658_ = l_List_reverse___redArg(v_a_657_);
return v___x_658_;
}
else
{
lean_object* v_head_659_; uint8_t v_isFun_660_; 
v_head_659_ = lean_ctor_get(v_a_656_, 0);
v_isFun_660_ = lean_ctor_get_uint8(v_head_659_, sizeof(void*)*2);
if (v_isFun_660_ == 0)
{
lean_object* v_tail_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_669_; 
lean_inc(v_head_659_);
v_tail_661_ = lean_ctor_get(v_a_656_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v_a_656_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; 
v_unused_670_ = lean_ctor_get(v_a_656_, 0);
lean_dec(v_unused_670_);
v___x_663_ = v_a_656_;
v_isShared_664_ = v_isSharedCheck_669_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_tail_661_);
lean_dec(v_a_656_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_669_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v_a_657_);
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_head_659_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_a_657_);
v___x_666_ = v_reuseFailAlloc_668_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
v_a_656_ = v_tail_661_;
v_a_657_ = v___x_666_;
goto _start;
}
}
}
else
{
lean_object* v_tail_671_; 
v_tail_671_ = lean_ctor_get(v_a_656_, 1);
lean_inc(v_tail_671_);
lean_dec_ref_known(v_a_656_, 2);
v_a_656_ = v_tail_671_;
goto _start;
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg(lean_object* v_k_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_676_ = lean_st_ref_get(v_a_674_);
v___x_677_ = lean_box(0);
v___x_678_ = l_List_filterTR_loop___at___00Lean_Compiler_LCNF_PullFunDecls_attachJps_spec__0(v___x_676_, v___x_677_);
v___x_679_ = lean_st_ref_take(v_a_674_);
v___x_680_ = l_List_filterTR_loop___at___00Lean_Compiler_LCNF_PullFunDecls_attachJps_spec__1(v___x_679_, v___x_677_);
v___x_681_ = lean_st_ref_put(v_a_674_, v___x_680_);
v___x_682_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___closed__0));
v___x_683_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(v___x_678_, v___x_682_, v_a_674_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_692_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_692_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = l_Lean_Compiler_LCNF_PullFunDecls_attach(v_a_684_, v_k_673_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_688_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_dec_ref(v_k_673_);
v_a_693_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_683_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_683_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_673_ = stack[0].m_obj;
lean_object* v_a_674_ = stack[1].m_obj;
lean_object* v_res_701_;
v_res_701_ = l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg(v_k_673_, v_a_674_);
stack->m_obj
 = v_res_701_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg___boxed(lean_object* v_k_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg(v_k_702_, v_a_703_);
lean_dec(v_a_703_);
return v_res_705_;
}
}
lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachJps(lean_object* v_k_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg(v_k_706_, v_a_707_);
return v___x_713_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PullFunDecls_attachJps_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_706_ = stack[0].m_obj;
lean_object* v_a_707_ = stack[1].m_obj;
lean_object* v_a_708_ = stack[2].m_obj;
lean_object* v_a_709_ = stack[3].m_obj;
lean_object* v_a_710_ = stack[4].m_obj;
lean_object* v_a_711_ = stack[5].m_obj;
lean_object* v_res_714_;
v_res_714_ = l_Lean_Compiler_LCNF_PullFunDecls_attachJps(v_k_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
stack->m_obj
 = v_res_714_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachJps___boxed(lean_object* v_k_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Compiler_LCNF_PullFunDecls_attachJps(v_k_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
return v_res_722_;
}
}
lean_object* l_Lean_Compiler_LCNF_PullFunDecls_addToPull(uint8_t v_isFun_723_, lean_object* v_decl_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v_params_736_; lean_object* v_type_737_; lean_object* v_value_738_; uint8_t v___x_739_; lean_object* v_value_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___x_768_; 
v___x_731_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_732_ = lean_st_ref_get(v_a_725_);
v___x_733_ = lean_st_ref_take(v_a_725_);
lean_dec(v___x_733_);
v___x_734_ = lean_box(0);
v___x_735_ = lean_st_ref_put(v_a_725_, v___x_734_);
v_params_736_ = lean_ctor_get(v_decl_724_, 2);
lean_inc_ref(v_params_736_);
v_type_737_ = lean_ctor_get(v_decl_724_, 3);
lean_inc_ref(v_type_737_);
v_value_738_ = lean_ctor_get(v_decl_724_, 4);
v___x_739_ = 0;
lean_inc_ref(v_value_738_);
v___x_768_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(v_value_738_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_770_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
v___x_770_ = l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(v_params_736_, v_a_769_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_);
if (lean_obj_tag(v___x_770_) == 0)
{
if (v_isFun_723_ == 0)
{
lean_object* v_a_771_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref_known(v___x_770_, 1);
v_value_741_ = v_a_771_;
v___y_742_ = v_a_725_;
v___y_743_ = v_a_727_;
goto v___jp_740_;
}
else
{
lean_object* v_a_772_; lean_object* v___x_773_; 
v_a_772_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_772_);
lean_dec_ref_known(v___x_770_, 1);
v___x_773_ = l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg(v_a_772_, v_a_725_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_773_, 1);
v_value_741_ = v_a_774_;
v___y_742_ = v_a_725_;
v___y_743_ = v_a_727_;
goto v___jp_740_;
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec_ref(v_type_737_);
lean_dec_ref(v_params_736_);
lean_dec(v___x_732_);
lean_dec_ref(v_decl_724_);
v_a_775_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_773_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_773_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec_ref(v_type_737_);
lean_dec_ref(v_params_736_);
lean_dec(v___x_732_);
lean_dec_ref(v_decl_724_);
v_a_783_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_770_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_770_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec_ref(v_type_737_);
lean_dec_ref(v_params_736_);
lean_dec(v___x_732_);
lean_dec_ref(v_decl_724_);
v_a_791_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_768_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_768_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
v___jp_740_:
{
lean_object* v___x_744_; 
v___x_744_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_739_, v_decl_724_, v_type_737_, v_params_736_, v_value_741_, v___y_743_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_759_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_759_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_759_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_759_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_749_ = lean_st_ref_take(v___y_742_);
v___x_750_ = lean_box(0);
lean_inc(v_a_745_);
v___x_751_ = l_Lean_Compiler_LCNF_FunDecl_collectUsed(v___x_739_, v_a_745_, v___x_731_);
v___x_752_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_752_, 0, v_a_745_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
lean_ctor_set_uint8(v___x_752_, sizeof(void*)*2, v_isFun_723_);
v___x_753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v___x_749_);
v___x_754_ = l_List_appendTR___redArg(v___x_753_, v___x_732_);
v___x_755_ = lean_st_ref_put(v___y_742_, v___x_754_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_750_);
v___x_757_ = v___x_747_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_750_);
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
lean_dec(v___x_732_);
v_a_760_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_744_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_744_);
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_PullFunDecls_addToPull_0interp(lean_interpreter_value* stack)
{
uint8_t v_isFun_723_ = stack[0].m_num;
lean_object* v_decl_724_ = stack[1].m_obj;
lean_object* v_a_725_ = stack[2].m_obj;
lean_object* v_a_726_ = stack[3].m_obj;
lean_object* v_a_727_ = stack[4].m_obj;
lean_object* v_a_728_ = stack[5].m_obj;
lean_object* v_a_729_ = stack[6].m_obj;
lean_object* v_res_799_;
v_res_799_ = l_Lean_Compiler_LCNF_PullFunDecls_addToPull(v_isFun_723_, v_decl_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_);
stack->m_obj
 = v_res_799_;
}
lean_object* l_Lean_Compiler_LCNF_PullFunDecls_pull(lean_object* v_code_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
switch(lean_obj_tag(v_code_800_))
{
case 0:
{
lean_object* v_decl_807_; lean_object* v_k_808_; lean_object* v___x_809_; 
v_decl_807_ = lean_ctor_get(v_code_800_, 0);
v_k_808_ = lean_ctor_get(v_code_800_, 1);
lean_inc_ref(v_k_808_);
v___x_809_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(v_k_808_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v_fvarId_811_; lean_object* v___x_812_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref_known(v___x_809_, 1);
v_fvarId_811_ = lean_ctor_get(v_decl_807_, 0);
v___x_812_ = l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg(v_fvarId_811_, v_a_810_, v_a_801_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_849_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_849_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_849_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_849_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
size_t v___x_817_; size_t v___x_818_; uint8_t v___x_819_; 
v___x_817_ = lean_ptr_addr(v_k_808_);
v___x_818_ = lean_ptr_addr(v_a_813_);
v___x_819_ = lean_usize_dec_eq(v___x_817_, v___x_818_);
if (v___x_819_ == 0)
{
lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_829_; 
lean_inc_ref(v_decl_807_);
v_isSharedCheck_829_ = !lean_is_exclusive(v_code_800_);
if (v_isSharedCheck_829_ == 0)
{
lean_object* v_unused_830_; lean_object* v_unused_831_; 
v_unused_830_ = lean_ctor_get(v_code_800_, 1);
lean_dec(v_unused_830_);
v_unused_831_ = lean_ctor_get(v_code_800_, 0);
lean_dec(v_unused_831_);
v___x_821_ = v_code_800_;
v_isShared_822_ = v_isSharedCheck_829_;
goto v_resetjp_820_;
}
else
{
lean_dec(v_code_800_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_829_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 1, v_a_813_);
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_decl_807_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_a_813_);
v___x_824_ = v_reuseFailAlloc_828_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_826_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_824_);
v___x_826_ = v___x_815_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
size_t v___x_832_; uint8_t v___x_833_; 
v___x_832_ = lean_ptr_addr(v_decl_807_);
v___x_833_ = lean_usize_dec_eq(v___x_832_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_843_; 
lean_inc_ref(v_decl_807_);
v_isSharedCheck_843_ = !lean_is_exclusive(v_code_800_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; lean_object* v_unused_845_; 
v_unused_844_ = lean_ctor_get(v_code_800_, 1);
lean_dec(v_unused_844_);
v_unused_845_ = lean_ctor_get(v_code_800_, 0);
lean_dec(v_unused_845_);
v___x_835_ = v_code_800_;
v_isShared_836_ = v_isSharedCheck_843_;
goto v_resetjp_834_;
}
else
{
lean_dec(v_code_800_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_843_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v_a_813_);
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_decl_807_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_a_813_);
v___x_838_ = v_reuseFailAlloc_842_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_840_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_838_);
v___x_840_ = v___x_815_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
else
{
lean_object* v___x_847_; 
lean_dec(v_a_813_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v_code_800_);
v___x_847_ = v___x_815_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_code_800_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_800_, 2);
return v___x_812_;
}
}
else
{
lean_dec_ref_known(v_code_800_, 2);
return v___x_809_;
}
}
case 1:
{
lean_object* v_decl_850_; lean_object* v_k_851_; uint8_t v___x_852_; lean_object* v___x_853_; 
v_decl_850_ = lean_ctor_get(v_code_800_, 0);
lean_inc_ref(v_decl_850_);
v_k_851_ = lean_ctor_get(v_code_800_, 1);
lean_inc_ref(v_k_851_);
lean_dec_ref_known(v_code_800_, 2);
v___x_852_ = 1;
v___x_853_ = l_Lean_Compiler_LCNF_PullFunDecls_addToPull(v___x_852_, v_decl_850_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_dec_ref_known(v___x_853_, 1);
v_code_800_ = v_k_851_;
goto _start;
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec_ref(v_k_851_);
v_a_855_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_853_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_853_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
case 2:
{
lean_object* v_decl_863_; lean_object* v_k_864_; uint8_t v___x_865_; lean_object* v___x_866_; 
v_decl_863_ = lean_ctor_get(v_code_800_, 0);
lean_inc_ref(v_decl_863_);
v_k_864_ = lean_ctor_get(v_code_800_, 1);
lean_inc_ref(v_k_864_);
lean_dec_ref_known(v_code_800_, 2);
v___x_865_ = 0;
v___x_866_ = l_Lean_Compiler_LCNF_PullFunDecls_addToPull(v___x_865_, v_decl_863_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_dec_ref_known(v___x_866_, 1);
v_code_800_ = v_k_864_;
goto _start;
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec_ref(v_k_864_);
v_a_868_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_866_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_866_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
case 4:
{
lean_object* v_cases_876_; lean_object* v_typeName_877_; lean_object* v_resultType_878_; lean_object* v_discr_879_; lean_object* v_alts_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_919_; 
v_cases_876_ = lean_ctor_get(v_code_800_, 0);
lean_inc_ref(v_cases_876_);
v_typeName_877_ = lean_ctor_get(v_cases_876_, 0);
v_resultType_878_ = lean_ctor_get(v_cases_876_, 1);
v_discr_879_ = lean_ctor_get(v_cases_876_, 2);
v_alts_880_ = lean_ctor_get(v_cases_876_, 3);
v_isSharedCheck_919_ = !lean_is_exclusive(v_cases_876_);
if (v_isSharedCheck_919_ == 0)
{
v___x_882_ = v_cases_876_;
v_isShared_883_ = v_isSharedCheck_919_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_alts_880_);
lean_inc(v_discr_879_);
lean_inc(v_resultType_878_);
lean_inc(v_typeName_877_);
lean_dec(v_cases_876_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_919_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_880_);
v___x_885_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullFunDecls_pull_spec__1(v___x_884_, v_alts_880_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_910_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_910_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_910_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_910_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
size_t v___x_890_; size_t v___x_891_; uint8_t v___x_892_; 
v___x_890_ = lean_ptr_addr(v_alts_880_);
lean_dec_ref(v_alts_880_);
v___x_891_ = lean_ptr_addr(v_a_886_);
v___x_892_ = lean_usize_dec_eq(v___x_890_, v___x_891_);
if (v___x_892_ == 0)
{
lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_905_; 
v_isSharedCheck_905_ = !lean_is_exclusive(v_code_800_);
if (v_isSharedCheck_905_ == 0)
{
lean_object* v_unused_906_; 
v_unused_906_ = lean_ctor_get(v_code_800_, 0);
lean_dec(v_unused_906_);
v___x_894_ = v_code_800_;
v_isShared_895_ = v_isSharedCheck_905_;
goto v_resetjp_893_;
}
else
{
lean_dec(v_code_800_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_905_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 3, v_a_886_);
v___x_897_ = v___x_882_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_typeName_877_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_resultType_878_);
lean_ctor_set(v_reuseFailAlloc_904_, 2, v_discr_879_);
lean_ctor_set(v_reuseFailAlloc_904_, 3, v_a_886_);
v___x_897_ = v_reuseFailAlloc_904_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_899_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_897_);
v___x_899_ = v___x_894_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_903_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_901_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_899_);
v___x_901_ = v___x_888_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
else
{
lean_object* v___x_908_; 
lean_dec(v_a_886_);
lean_del_object(v___x_882_);
lean_dec(v_discr_879_);
lean_dec_ref(v_resultType_878_);
lean_dec(v_typeName_877_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v_code_800_);
v___x_908_ = v___x_888_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_code_800_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_del_object(v___x_882_);
lean_dec_ref(v_alts_880_);
lean_dec(v_discr_879_);
lean_dec_ref(v_resultType_878_);
lean_dec(v_typeName_877_);
lean_dec_ref_known(v_code_800_, 1);
v_a_911_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_885_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_885_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
default: 
{
lean_object* v___x_920_; 
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v_code_800_);
return v___x_920_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PullFunDecls_pull_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_800_ = stack[0].m_obj;
lean_object* v_a_801_ = stack[1].m_obj;
lean_object* v_a_802_ = stack[2].m_obj;
lean_object* v_a_803_ = stack[3].m_obj;
lean_object* v_a_804_ = stack[4].m_obj;
lean_object* v_a_805_ = stack[5].m_obj;
lean_object* v_res_921_;
v_res_921_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(v_code_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
stack->m_obj
 = v_res_921_;
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullFunDecls_pull_spec__1(lean_object* v_i_922_, lean_object* v_as_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_930_ = lean_array_get_size(v_as_923_);
v___x_931_ = lean_nat_dec_lt(v_i_922_, v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; 
lean_dec(v_i_922_);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v_as_923_);
return v___x_932_;
}
else
{
lean_object* v_a_933_; lean_object* v_a_935_; 
v_a_933_ = lean_array_fget_borrowed(v_as_923_, v_i_922_);
if (lean_obj_tag(v_a_933_) == 0)
{
lean_object* v_params_946_; lean_object* v_code_947_; lean_object* v___x_948_; 
v_params_946_ = lean_ctor_get(v_a_933_, 1);
v_code_947_ = lean_ctor_get(v_a_933_, 2);
lean_inc_ref(v_code_947_);
v___x_948_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(v_code_947_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_950_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref_known(v___x_948_, 1);
v___x_950_ = l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(v_params_946_, v_a_949_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_952_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 1);
lean_inc_ref(v_a_933_);
v___x_952_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_933_, v_a_951_);
v_a_935_ = v___x_952_;
goto v___jp_934_;
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec_ref(v_as_923_);
lean_dec(v_i_922_);
v_a_953_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_950_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_950_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
lean_dec_ref(v_as_923_);
lean_dec(v_i_922_);
v_a_961_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_948_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_948_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
else
{
lean_object* v_code_969_; lean_object* v___x_970_; 
v_code_969_ = lean_ctor_get(v_a_933_, 0);
lean_inc_ref(v_code_969_);
v___x_970_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(v_code_969_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_972_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
lean_dec_ref_known(v___x_970_, 1);
lean_inc_ref(v_a_933_);
v___x_972_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_933_, v_a_971_);
v_a_935_ = v___x_972_;
goto v___jp_934_;
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec_ref(v_as_923_);
lean_dec(v_i_922_);
v_a_973_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_970_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_970_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
v___jp_934_:
{
size_t v___x_936_; size_t v___x_937_; uint8_t v___x_938_; 
v___x_936_ = lean_ptr_addr(v_a_933_);
v___x_937_ = lean_ptr_addr(v_a_935_);
v___x_938_ = lean_usize_dec_eq(v___x_936_, v___x_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_nat_add(v_i_922_, v___x_939_);
v___x_941_ = lean_array_fset(v_as_923_, v_i_922_, v_a_935_);
lean_dec(v_i_922_);
v_i_922_ = v___x_940_;
v_as_923_ = v___x_941_;
goto _start;
}
else
{
lean_object* v___x_943_; lean_object* v___x_944_; 
lean_dec_ref(v_a_935_);
v___x_943_ = lean_unsigned_to_nat(1u);
v___x_944_ = lean_nat_add(v_i_922_, v___x_943_);
lean_dec(v_i_922_);
v_i_922_ = v___x_944_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullFunDecls_pull_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_922_ = stack[0].m_obj;
lean_object* v_as_923_ = stack[1].m_obj;
lean_object* v___y_924_ = stack[2].m_obj;
lean_object* v___y_925_ = stack[3].m_obj;
lean_object* v___y_926_ = stack[4].m_obj;
lean_object* v___y_927_ = stack[5].m_obj;
lean_object* v___y_928_ = stack[6].m_obj;
lean_object* v_res_981_;
v_res_981_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullFunDecls_pull_spec__1(v_i_922_, v_as_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
stack->m_obj
 = v_res_981_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullFunDecls_pull_spec__1___boxed(lean_object* v_i_982_, lean_object* v_as_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullFunDecls_pull_spec__1(v_i_982_, v_as_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_addToPull___boxed(lean_object* v_isFun_991_, lean_object* v_decl_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
uint8_t v_isFun_boxed_999_; lean_object* v_res_1000_; 
v_isFun_boxed_999_ = lean_unbox(v_isFun_991_);
v_res_1000_ = l_Lean_Compiler_LCNF_PullFunDecls_addToPull(v_isFun_boxed_999_, v_decl_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
lean_dec(v_a_993_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_pull___boxed(lean_object* v_code_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(v_code_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
lean_dec(v_a_1002_);
return v_res_1008_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg(lean_object* v_f_1009_, lean_object* v_v_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
if (lean_obj_tag(v_v_1010_) == 0)
{
lean_object* v_code_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1041_; 
v_code_1017_ = lean_ctor_get(v_v_1010_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_v_1010_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1019_ = v_v_1010_;
v_isShared_1020_ = v_isSharedCheck_1041_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_code_1017_);
lean_dec(v_v_1010_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1041_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; 
lean_inc(v___y_1015_);
lean_inc_ref(v___y_1014_);
lean_inc(v___y_1013_);
lean_inc_ref(v___y_1012_);
lean_inc(v___y_1011_);
v___x_1021_ = lean_apply_7(v_f_1009_, v_code_1017_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, lean_box(0));
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1032_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1024_ = v___x_1021_;
v_isShared_1025_ = v_isSharedCheck_1032_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1032_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v_a_1022_);
v___x_1027_ = v___x_1019_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1029_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1027_);
v___x_1029_ = v___x_1024_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
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
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_del_object(v___x_1019_);
v_a_1033_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1021_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1021_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
else
{
lean_object* v___x_1042_; 
lean_dec_ref(v_f_1009_);
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v_v_1010_);
return v___x_1042_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1009_ = stack[0].m_obj;
lean_object* v_v_1010_ = stack[1].m_obj;
lean_object* v___y_1011_ = stack[2].m_obj;
lean_object* v___y_1012_ = stack[3].m_obj;
lean_object* v___y_1013_ = stack[4].m_obj;
lean_object* v___y_1014_ = stack[5].m_obj;
lean_object* v___y_1015_ = stack[6].m_obj;
lean_object* v_res_1043_;
v_res_1043_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg(v_f_1009_, v_v_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
stack->m_obj
 = v_res_1043_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg___boxed(lean_object* v_f_1044_, lean_object* v_v_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg(v_f_1044_, v_v_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
return v_res_1052_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0(uint8_t v_pu_1053_, lean_object* v_f_1054_, lean_object* v_v_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg(v_f_1054_, v_v_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1053_ = stack[0].m_num;
lean_object* v_f_1054_ = stack[1].m_obj;
lean_object* v_v_1055_ = stack[2].m_obj;
lean_object* v___y_1056_ = stack[3].m_obj;
lean_object* v___y_1057_ = stack[4].m_obj;
lean_object* v___y_1058_ = stack[5].m_obj;
lean_object* v___y_1059_ = stack[6].m_obj;
lean_object* v___y_1060_ = stack[7].m_obj;
lean_object* v_res_1063_;
v_res_1063_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0(v_pu_1053_, v_f_1054_, v_v_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
stack->m_obj
 = v_res_1063_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___boxed(lean_object* v_pu_1064_, lean_object* v_f_1065_, lean_object* v_v_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
uint8_t v_pu_boxed_1073_; lean_object* v_res_1074_; 
v_pu_boxed_1073_ = lean_unbox(v_pu_1064_);
v_res_1074_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0(v_pu_boxed_1073_, v_f_1065_, v_v_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
return v_res_1074_;
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_pullFunDecls(lean_object* v_decl_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v_toSignature_1082_; lean_object* v_value_1083_; uint8_t v_recursive_1084_; lean_object* v_inlineAttr_x3f_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1116_; 
v_toSignature_1082_ = lean_ctor_get(v_decl_1076_, 0);
v_value_1083_ = lean_ctor_get(v_decl_1076_, 1);
v_recursive_1084_ = lean_ctor_get_uint8(v_decl_1076_, sizeof(void*)*3);
v_inlineAttr_x3f_1085_ = lean_ctor_get(v_decl_1076_, 2);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_decl_1076_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1087_ = v_decl_1076_;
v_isShared_1088_ = v_isSharedCheck_1116_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_inlineAttr_x3f_1085_);
lean_inc(v_value_1083_);
lean_inc(v_toSignature_1082_);
lean_dec(v_decl_1076_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1116_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1089_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_pullFunDecls___closed__0));
v___x_1090_ = lean_box(0);
v___x_1091_ = lean_st_mk_ref(v___x_1090_);
v___x_1092_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg(v___x_1089_, v_value_1083_, v___x_1091_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1107_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1107_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1107_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1097_ = lean_st_ref_get(v___x_1091_);
lean_dec(v___x_1091_);
v___x_1098_ = lean_array_mk(v___x_1097_);
v___x_1099_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PullFunDecls_attach), 2, 1);
lean_closure_set(v___x_1099_, 0, v___x_1098_);
v___x_1100_ = l_Lean_Compiler_LCNF_DeclValue_mapCode___redArg(v___x_1099_, v_a_1093_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 1, v___x_1100_);
v___x_1102_ = v___x_1087_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_toSignature_1082_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v_inlineAttr_x3f_1085_);
lean_ctor_set_uint8(v_reuseFailAlloc_1106_, sizeof(void*)*3, v_recursive_1084_);
v___x_1102_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1104_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1102_);
v___x_1104_ = v___x_1095_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec(v___x_1091_);
lean_del_object(v___x_1087_);
lean_dec(v_inlineAttr_x3f_1085_);
lean_dec_ref(v_toSignature_1082_);
v_a_1108_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1092_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1092_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Decl_pullFunDecls_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1076_ = stack[0].m_obj;
lean_object* v_a_1077_ = stack[1].m_obj;
lean_object* v_a_1078_ = stack[2].m_obj;
lean_object* v_a_1079_ = stack[3].m_obj;
lean_object* v_a_1080_ = stack[4].m_obj;
lean_object* v_res_1117_;
v_res_1117_ = l_Lean_Compiler_LCNF_Decl_pullFunDecls(v_decl_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
stack->m_obj
 = v_res_1117_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullFunDecls___boxed(lean_object* v_decl_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Compiler_LCNF_Decl_pullFunDecls(v_decl_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
return v_res_1124_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullFunDecls___closed__3(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1129_ = lean_unsigned_to_nat(0u);
v___x_1130_ = ((lean_object*)(l_Lean_Compiler_LCNF_pullFunDecls___closed__2));
v___x_1131_ = 0;
v___x_1132_ = ((lean_object*)(l_Lean_Compiler_LCNF_pullFunDecls___closed__1));
v___x_1133_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1132_, v___x_1131_, v___x_1130_, v___x_1129_);
return v___x_1133_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullFunDecls(void){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_obj_once(&l_Lean_Compiler_LCNF_pullFunDecls___closed__3, &l_Lean_Compiler_LCNF_pullFunDecls___closed__3_once, _init_l_Lean_Compiler_LCNF_pullFunDecls___closed__3);
return v___x_1134_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1205_; uint8_t v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1205_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_));
v___x_1206_ = 1;
v___x_1207_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_));
v___x_1208_ = l_Lean_registerTraceClass(v___x_1205_, v___x_1206_, v___x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1209_;
v_res_1209_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1209_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2____boxed(lean_object* v_a_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_();
return v_res_1211_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_PullFunDecls(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_DependsOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default = _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default();
lean_mark_persistent(l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default);
l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull = _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull();
lean_mark_persistent(l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull);
l_Lean_Compiler_LCNF_pullFunDecls = _init_l_Lean_Compiler_LCNF_pullFunDecls();
lean_mark_persistent(l_Lean_Compiler_LCNF_pullFunDecls);
res = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_PullFunDecls(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_PullFunDecls(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_DependsOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PullFunDecls(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_PullFunDecls(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_PullFunDecls(builtin);
}
#ifdef __cplusplus
}
#endif
