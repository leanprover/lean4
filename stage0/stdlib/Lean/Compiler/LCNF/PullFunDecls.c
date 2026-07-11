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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1(uint8_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDecl_collectUsed(uint8_t, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
uint8_t v___x_1_; lean_object* v___x_2_; 
v___x_1_ = 0;
v___x_2_ = l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; uint8_t v___x_5_; lean_object* v___x_6_; 
v___x_3_ = l_Lean_instInhabitedFVarIdHashSet;
v___x_4_ = lean_obj_once(&l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__0, &l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__0_once, _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__0);
v___x_5_ = 0;
v___x_6_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_6_, 0, v___x_4_);
lean_ctor_set(v___x_6_, 1, v___x_3_);
lean_ctor_set_uint8(v___x_6_, sizeof(void*)*2, v___x_5_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_once(&l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__1, &l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__1_once, _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default___closed__1);
return v___x_7_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default;
return v___x_8_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___redArg(lean_object* v_a_9_, lean_object* v_x_10_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
uint8_t v___x_11_; 
v___x_11_ = 0;
return v___x_11_;
}
else
{
lean_object* v_key_12_; lean_object* v_tail_13_; uint8_t v___x_14_; 
v_key_12_ = lean_ctor_get(v_x_10_, 0);
v_tail_13_ = lean_ctor_get(v_x_10_, 2);
v___x_14_ = l_Lean_instBEqFVarId_beq(v_key_12_, v_a_9_);
if (v___x_14_ == 0)
{
v_x_10_ = v_tail_13_;
goto _start;
}
else
{
return v___x_14_;
}
}
}
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(lean_object* v_m_20_, lean_object* v_a_21_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg___boxed(lean_object* v_m_38_, lean_object* v_a_39_){
_start:
{
uint8_t v_res_40_; lean_object* v_r_41_; 
v_res_40_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(v_m_38_, v_a_39_);
lean_dec(v_a_39_);
lean_dec_ref(v_m_38_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg(lean_object* v_fvarId_42_, lean_object* v_as_43_, lean_object* v_keep_44_, lean_object* v_dep_45_){
_start:
{
if (lean_obj_tag(v_as_43_) == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v_keep_44_);
lean_ctor_set(v___x_47_, 1, v_dep_45_);
v___x_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
return v___x_48_;
}
else
{
lean_object* v_head_49_; lean_object* v_tail_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_64_; 
v_head_49_ = lean_ctor_get(v_as_43_, 0);
v_tail_50_ = lean_ctor_get(v_as_43_, 1);
v_isSharedCheck_64_ = !lean_is_exclusive(v_as_43_);
if (v_isSharedCheck_64_ == 0)
{
v___x_52_ = v_as_43_;
v_isShared_53_ = v_isSharedCheck_64_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_tail_50_);
lean_inc(v_head_49_);
lean_dec(v_as_43_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_64_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v_used_54_; uint8_t v___x_55_; 
v_used_54_ = lean_ctor_get(v_head_49_, 1);
v___x_55_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(v_used_54_, v_fvarId_42_);
if (v___x_55_ == 0)
{
lean_object* v___x_57_; 
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 1, v_keep_44_);
v___x_57_ = v___x_52_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_head_49_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v_keep_44_);
v___x_57_ = v_reuseFailAlloc_59_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
v_as_43_ = v_tail_50_;
v_keep_44_ = v___x_57_;
goto _start;
}
}
else
{
lean_object* v___x_61_; 
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 1, v_dep_45_);
v___x_61_ = v___x_52_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_head_49_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_dep_45_);
v___x_61_ = v_reuseFailAlloc_63_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
v_as_43_ = v_tail_50_;
v_dep_45_ = v___x_61_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg___boxed(lean_object* v_fvarId_65_, lean_object* v_as_66_, lean_object* v_keep_67_, lean_object* v_dep_68_, lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg(v_fvarId_65_, v_as_66_, v_keep_67_, v_dep_68_);
lean_dec(v_fvarId_65_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go(lean_object* v_fvarId_71_, lean_object* v_as_72_, lean_object* v_keep_73_, lean_object* v_dep_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg(v_fvarId_71_, v_as_72_, v_keep_73_, v_dep_74_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___boxed(lean_object* v_fvarId_79_, lean_object* v_as_80_, lean_object* v_keep_81_, lean_object* v_dep_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go(v_fvarId_79_, v_as_80_, v_keep_81_, v_dep_82_, v_a_83_, v_a_84_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
lean_dec(v_fvarId_79_);
return v_res_86_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0(lean_object* v_00_u03b2_87_, lean_object* v_m_88_, lean_object* v_a_89_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(v_m_88_, v_a_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___boxed(lean_object* v_00_u03b2_91_, lean_object* v_m_92_, lean_object* v_a_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0(v_00_u03b2_91_, v_m_92_, v_a_93_);
lean_dec(v_a_93_);
lean_dec_ref(v_m_92_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0(lean_object* v_00_u03b2_96_, lean_object* v_a_97_, lean_object* v_x_98_){
_start:
{
uint8_t v___x_99_; 
v___x_99_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___redArg(v_a_97_, v_x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_100_, lean_object* v_a_101_, lean_object* v_x_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0_spec__0(v_00_u03b2_100_, v_a_101_, v_x_102_);
lean_dec(v_x_102_);
lean_dec(v_a_101_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_spec__0(lean_object* v_fvarId_105_, lean_object* v_x_106_){
_start:
{
if (lean_obj_tag(v_x_106_) == 0)
{
uint8_t v___x_107_; 
v___x_107_ = 0;
return v___x_107_;
}
else
{
lean_object* v_head_108_; lean_object* v_tail_109_; lean_object* v_used_110_; uint8_t v___x_111_; 
v_head_108_ = lean_ctor_get(v_x_106_, 0);
v_tail_109_ = lean_ctor_get(v_x_106_, 1);
v_used_110_ = lean_ctor_get(v_head_108_, 1);
v___x_111_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(v_used_110_, v_fvarId_105_);
if (v___x_111_ == 0)
{
v_x_106_ = v_tail_109_;
goto _start;
}
else
{
return v___x_111_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_spec__0___boxed(lean_object* v_fvarId_113_, lean_object* v_x_114_){
_start:
{
uint8_t v_res_115_; lean_object* v_r_116_; 
v_res_115_ = l_List_any___at___00Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_spec__0(v_fvarId_113_, v_x_114_);
lean_dec(v_x_114_);
lean_dec(v_fvarId_113_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(lean_object* v_fvarId_117_, lean_object* v_a_118_){
_start:
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = lean_st_ref_get(v_a_118_);
v___x_121_ = l_List_any___at___00Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_spec__0(v_fvarId_117_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec(v___x_120_);
v___x_122_ = lean_box(0);
v___x_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
return v___x_123_;
}
else
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_136_; 
v___x_124_ = lean_box(0);
v___x_125_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go___redArg(v_fvarId_117_, v___x_120_, v___x_124_, v___x_124_);
v_a_126_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_136_ == 0)
{
v___x_128_ = v___x_125_;
v_isShared_129_ = v_isSharedCheck_136_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v___x_125_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_136_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v_fst_130_; lean_object* v_snd_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v_fst_130_ = lean_ctor_get(v_a_126_, 0);
lean_inc(v_fst_130_);
v_snd_131_ = lean_ctor_get(v_a_126_, 1);
lean_inc(v_snd_131_);
lean_dec(v_a_126_);
v___x_132_ = lean_st_ref_set(v_a_118_, v_fst_130_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 0, v_snd_131_);
v___x_134_ = v___x_128_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_snd_131_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg___boxed(lean_object* v_fvarId_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(v_fvarId_137_, v_a_138_);
lean_dec(v_a_138_);
lean_dec(v_fvarId_137_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps(lean_object* v_fvarId_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(v_fvarId_141_, v_a_142_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___boxed(lean_object* v_fvarId_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps(v_fvarId_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
lean_dec(v_fvarId_149_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(lean_object* v_todo_157_, lean_object* v_acc_158_, lean_object* v_a_159_){
_start:
{
if (lean_obj_tag(v_todo_157_) == 0)
{
lean_object* v___x_161_; 
v___x_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_161_, 0, v_acc_158_);
return v___x_161_;
}
else
{
lean_object* v_head_162_; lean_object* v_decl_163_; lean_object* v_tail_164_; lean_object* v_fvarId_165_; lean_object* v___x_166_; 
v_head_162_ = lean_ctor_get(v_todo_157_, 0);
lean_inc(v_head_162_);
v_decl_163_ = lean_ctor_get(v_head_162_, 0);
v_tail_164_ = lean_ctor_get(v_todo_157_, 1);
lean_inc(v_tail_164_);
lean_dec_ref_known(v_todo_157_, 2);
v_fvarId_165_ = lean_ctor_get(v_decl_163_, 0);
v___x_166_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(v_fvarId_165_, v_a_159_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_a_167_);
lean_dec_ref_known(v___x_166_, 1);
v___x_168_ = l_List_appendTR___redArg(v_a_167_, v_tail_164_);
v___x_169_ = lean_array_push(v_acc_158_, v_head_162_);
v_todo_157_ = v___x_168_;
v_acc_158_ = v___x_169_;
goto _start;
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_dec(v_tail_164_);
lean_dec(v_head_162_);
lean_dec_ref(v_acc_158_);
v_a_171_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_166_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_166_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg___boxed(lean_object* v_todo_179_, lean_object* v_acc_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(v_todo_179_, v_acc_180_, v_a_181_);
lean_dec(v_a_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint(lean_object* v_todo_184_, lean_object* v_acc_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(v_todo_184_, v_acc_185_, v_a_186_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___boxed(lean_object* v_todo_193_, lean_object* v_acc_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint(v_todo_193_, v_acc_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_a_195_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(lean_object* v_fvarId_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps___redArg(v_fvarId_204_, v_a_205_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
lean_dec_ref_known(v___x_207_, 1);
v___x_209_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___closed__0));
v___x_210_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(v_a_208_, v___x_209_, v_a_205_);
return v___x_210_;
}
else
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
v_a_211_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_218_ == 0)
{
v___x_213_ = v___x_207_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_207_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_211_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___boxed(lean_object* v_fvarId_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(v_fvarId_219_, v_a_220_);
lean_dec(v_a_220_);
lean_dec(v_fvarId_219_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps(lean_object* v_fvarId_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(v_fvarId_223_, v_a_224_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___boxed(lean_object* v_fvarId_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps(v_fvarId_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec(v_a_232_);
lean_dec(v_fvarId_231_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg(lean_object* v_as_239_, size_t v_sz_240_, size_t v_i_241_, lean_object* v_b_242_, lean_object* v___y_243_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = lean_usize_dec_lt(v_i_241_, v_sz_240_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; 
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v_b_242_);
return v___x_246_;
}
else
{
lean_object* v_a_247_; lean_object* v_fvarId_248_; lean_object* v___x_249_; 
v_a_247_ = lean_array_uget_borrowed(v_as_239_, v_i_241_);
v_fvarId_248_ = lean_ctor_get(v_a_247_, 0);
v___x_249_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(v_fvarId_248_, v___y_243_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_251_; size_t v___x_252_; size_t v___x_253_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_250_);
lean_dec_ref_known(v___x_249_, 1);
v___x_251_ = l_Array_append___redArg(v_b_242_, v_a_250_);
lean_dec(v_a_250_);
v___x_252_ = ((size_t)1ULL);
v___x_253_ = lean_usize_add(v_i_241_, v___x_252_);
v_i_241_ = v___x_253_;
v_b_242_ = v___x_251_;
goto _start;
}
else
{
lean_dec_ref(v_b_242_);
return v___x_249_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg___boxed(lean_object* v_as_255_, lean_object* v_sz_256_, lean_object* v_i_257_, lean_object* v_b_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
size_t v_sz_boxed_261_; size_t v_i_boxed_262_; lean_object* v_res_263_; 
v_sz_boxed_261_ = lean_unbox_usize(v_sz_256_);
lean_dec(v_sz_256_);
v_i_boxed_262_ = lean_unbox_usize(v_i_257_);
lean_dec(v_i_257_);
v_res_263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg(v_as_255_, v_sz_boxed_261_, v_i_boxed_262_, v_b_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v_as_255_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg(lean_object* v_params_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_acc_271_; size_t v_sz_272_; size_t v___x_273_; lean_object* v___x_274_; 
v_acc_271_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___closed__0));
v_sz_272_ = lean_array_size(v_params_264_);
v___x_273_ = ((size_t)0ULL);
v___x_274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg(v_params_264_, v_sz_272_, v___x_273_, v_acc_271_, v_a_265_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg___boxed(lean_object* v_params_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg(v_params_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_params_275_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps(uint8_t v_pu_283_, lean_object* v_params_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg(v_params_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___boxed(lean_object* v_pu_292_, lean_object* v_params_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
uint8_t v_pu_boxed_300_; lean_object* v_res_301_; 
v_pu_boxed_300_ = lean_unbox(v_pu_292_);
v_res_301_ = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps(v_pu_boxed_300_, v_params_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_params_293_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0(lean_object* v_as_302_, size_t v_sz_303_, size_t v_i_304_, lean_object* v_b_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___redArg(v_as_302_, v_sz_303_, v_i_304_, v_b_305_, v___y_306_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0___boxed(lean_object* v_as_313_, lean_object* v_sz_314_, lean_object* v_i_315_, lean_object* v_b_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
size_t v_sz_boxed_323_; size_t v_i_boxed_324_; lean_object* v_res_325_; 
v_sz_boxed_323_ = lean_unbox_usize(v_sz_314_);
lean_dec(v_sz_314_);
v_i_boxed_324_ = lean_unbox_usize(v_i_315_);
lean_dec(v_i_315_);
v_res_325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_spec__0(v_as_313_, v_sz_boxed_323_, v_i_boxed_324_, v_b_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v_as_313_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach(lean_object* v_p_326_, lean_object* v_k_327_){
_start:
{
uint8_t v_isFun_328_; 
v_isFun_328_ = lean_ctor_get_uint8(v_p_326_, sizeof(void*)*2);
if (v_isFun_328_ == 0)
{
lean_object* v_decl_329_; lean_object* v___x_330_; 
v_decl_329_ = lean_ctor_get(v_p_326_, 0);
lean_inc_ref(v_decl_329_);
v___x_330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_330_, 0, v_decl_329_);
lean_ctor_set(v___x_330_, 1, v_k_327_);
return v___x_330_;
}
else
{
lean_object* v_decl_331_; lean_object* v___x_332_; 
v_decl_331_ = lean_ctor_get(v_p_326_, 0);
lean_inc_ref(v_decl_331_);
v___x_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_332_, 0, v_decl_331_);
lean_ctor_set(v___x_332_, 1, v_k_327_);
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach___boxed(lean_object* v_p_333_, lean_object* v_k_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach(v_p_333_, v_k_334_);
lean_dec_ref(v_p_333_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited(lean_object* v_i_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_snd_338_; uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_snd_338_ = lean_ctor_get(v_a_337_, 1);
v___x_339_ = 0;
v___x_340_ = lean_box(v___x_339_);
v___x_341_ = lean_array_get(v___x_340_, v_snd_338_, v_i_336_);
lean_dec(v___x_340_);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v_a_337_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited___boxed(lean_object* v_i_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited(v_i_343_, v_a_344_);
lean_dec(v_i_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg(lean_object* v_upperBound_346_, lean_object* v___x_347_, lean_object* v_ps_348_, lean_object* v_a_349_, lean_object* v_b_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_a_353_; lean_object* v_snd_354_; uint8_t v___x_358_; 
v___x_358_ = lean_nat_dec_lt(v_a_349_, v_upperBound_346_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; 
lean_dec(v_a_349_);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v_b_350_);
lean_ctor_set(v___x_359_, 1, v___y_351_);
return v___x_359_;
}
else
{
lean_object* v___x_360_; lean_object* v_fst_361_; lean_object* v_snd_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_360_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited(v_a_349_, v___y_351_);
v_fst_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_fst_361_);
v_snd_362_ = lean_ctor_get(v___x_360_, 1);
lean_inc(v_snd_362_);
lean_dec_ref(v___x_360_);
v___x_363_ = lean_box(0);
v___x_364_ = lean_unbox(v_fst_361_);
lean_dec(v_fst_361_);
if (v___x_364_ == 0)
{
lean_object* v_decl_365_; lean_object* v_fvarId_366_; lean_object* v___x_367_; lean_object* v_used_368_; uint8_t v___x_369_; 
v_decl_365_ = lean_ctor_get(v___x_347_, 0);
v_fvarId_366_ = lean_ctor_get(v_decl_365_, 0);
v___x_367_ = lean_array_fget_borrowed(v_ps_348_, v_a_349_);
v_used_368_ = lean_ctor_get(v___x_367_, 1);
v___x_369_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_findFVarDirectDeps_go_spec__0___redArg(v_used_368_, v_fvarId_366_);
if (v___x_369_ == 0)
{
v_a_353_ = v___x_363_;
v_snd_354_ = v_snd_362_;
goto v___jp_352_;
}
else
{
lean_object* v___x_370_; lean_object* v_snd_371_; 
v___x_370_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit(v_ps_348_, v_a_349_, v_snd_362_);
v_snd_371_ = lean_ctor_get(v___x_370_, 1);
lean_inc(v_snd_371_);
lean_dec_ref(v___x_370_);
v_a_353_ = v___x_363_;
v_snd_354_ = v_snd_371_;
goto v___jp_352_;
}
}
else
{
v_a_353_ = v___x_363_;
v_snd_354_ = v_snd_362_;
goto v___jp_352_;
}
}
v___jp_352_:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_unsigned_to_nat(1u);
v___x_356_ = lean_nat_add(v_a_349_, v___x_355_);
lean_dec(v_a_349_);
v_a_349_ = v___x_356_;
v_b_350_ = v_a_353_;
v___y_351_ = v_snd_354_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit(lean_object* v_ps_372_, lean_object* v_i_373_, lean_object* v_a_374_){
_start:
{
lean_object* v___x_375_; lean_object* v_fst_376_; uint8_t v___x_377_; 
v___x_375_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visited(v_i_373_, v_a_374_);
v_fst_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_fst_376_);
v___x_377_ = lean_unbox(v_fst_376_);
lean_dec(v_fst_376_);
if (v___x_377_ == 0)
{
lean_object* v_snd_378_; lean_object* v_fst_379_; lean_object* v_snd_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_415_; 
v_snd_378_ = lean_ctor_get(v___x_375_, 1);
lean_inc(v_snd_378_);
lean_dec_ref(v___x_375_);
v_fst_379_ = lean_ctor_get(v_snd_378_, 0);
v_snd_380_ = lean_ctor_get(v_snd_378_, 1);
v_isSharedCheck_415_ = !lean_is_exclusive(v_snd_378_);
if (v_isSharedCheck_415_ == 0)
{
v___x_382_ = v_snd_378_;
v_isShared_383_ = v_isSharedCheck_415_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_snd_380_);
lean_inc(v_fst_379_);
lean_dec(v_snd_378_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_415_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_384_ = l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull_default;
v___x_385_ = lean_array_get_size(v_ps_372_);
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = 1;
v___x_388_ = lean_box(v___x_387_);
v___x_389_ = lean_array_set(v_snd_380_, v_i_373_, v___x_388_);
v___x_390_ = lean_array_get_borrowed(v___x_384_, v_ps_372_, v_i_373_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 1, v___x_389_);
v___x_392_ = v___x_382_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_fst_379_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v___x_389_);
v___x_392_ = v_reuseFailAlloc_414_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v_snd_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_412_; 
v___x_393_ = lean_box(0);
v___x_394_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg(v___x_385_, v___x_390_, v_ps_372_, v___x_386_, v___x_393_, v___x_392_);
v_snd_395_ = lean_ctor_get(v___x_394_, 1);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; 
v_unused_413_ = lean_ctor_get(v___x_394_, 0);
lean_dec(v_unused_413_);
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_412_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_snd_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_412_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v_fst_399_; lean_object* v_snd_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_411_; 
v_fst_399_ = lean_ctor_get(v_snd_395_, 0);
v_snd_400_ = lean_ctor_get(v_snd_395_, 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v_snd_395_);
if (v_isSharedCheck_411_ == 0)
{
v___x_402_ = v_snd_395_;
v_isShared_403_ = v_isSharedCheck_411_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_snd_400_);
lean_inc(v_fst_399_);
lean_dec(v_snd_395_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_411_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach(v___x_390_, v_fst_399_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_404_);
v___x_406_ = v___x_402_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_snd_400_);
v___x_406_ = v_reuseFailAlloc_410_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_408_; 
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 1, v___x_406_);
lean_ctor_set(v___x_397_, 0, v___x_393_);
v___x_408_ = v___x_397_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
}
}
else
{
lean_object* v_snd_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_424_; 
v_snd_416_ = lean_ctor_get(v___x_375_, 1);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v___x_375_, 0);
lean_dec(v_unused_425_);
v___x_418_ = v___x_375_;
v_isShared_419_ = v_isSharedCheck_424_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_snd_416_);
lean_dec(v___x_375_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_424_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_420_ = lean_box(0);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_420_);
v___x_422_ = v___x_418_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_snd_416_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit___boxed(lean_object* v_ps_426_, lean_object* v_i_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit(v_ps_426_, v_i_427_, v_a_428_);
lean_dec(v_i_427_);
lean_dec_ref(v_ps_426_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg___boxed(lean_object* v_upperBound_430_, lean_object* v___x_431_, lean_object* v_ps_432_, lean_object* v_a_433_, lean_object* v_b_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg(v_upperBound_430_, v___x_431_, v_ps_432_, v_a_433_, v_b_434_, v___y_435_);
lean_dec_ref(v_ps_432_);
lean_dec_ref(v___x_431_);
lean_dec(v_upperBound_430_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0(lean_object* v_upperBound_437_, lean_object* v___x_438_, lean_object* v_ps_439_, lean_object* v_inst_440_, lean_object* v_R_441_, lean_object* v_a_442_, lean_object* v_b_443_, lean_object* v_c_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___redArg(v_upperBound_437_, v___x_438_, v_ps_439_, v_a_442_, v_b_443_, v___y_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0___boxed(lean_object* v_upperBound_447_, lean_object* v___x_448_, lean_object* v_ps_449_, lean_object* v_inst_450_, lean_object* v_R_451_, lean_object* v_a_452_, lean_object* v_b_453_, lean_object* v_c_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit_spec__0(v_upperBound_447_, v___x_448_, v_ps_449_, v_inst_450_, v_R_451_, v_a_452_, v_b_453_, v_c_454_, v___y_455_);
lean_dec_ref(v_ps_449_);
lean_dec_ref(v___x_448_);
lean_dec(v_upperBound_447_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg(lean_object* v_upperBound_457_, lean_object* v_ps_458_, lean_object* v_a_459_, lean_object* v_b_460_, lean_object* v___y_461_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = lean_nat_dec_lt(v_a_459_, v_upperBound_457_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; 
lean_dec(v_a_459_);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v_b_460_);
lean_ctor_set(v___x_463_, 1, v___y_461_);
return v___x_463_;
}
else
{
lean_object* v___x_464_; lean_object* v_snd_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_464_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_visit(v_ps_458_, v_a_459_, v___y_461_);
v_snd_465_ = lean_ctor_get(v___x_464_, 1);
lean_inc(v_snd_465_);
lean_dec_ref(v___x_464_);
v___x_466_ = lean_box(0);
v___x_467_ = lean_unsigned_to_nat(1u);
v___x_468_ = lean_nat_add(v_a_459_, v___x_467_);
lean_dec(v_a_459_);
v_a_459_ = v___x_468_;
v_b_460_ = v___x_466_;
v___y_461_ = v_snd_465_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg___boxed(lean_object* v_upperBound_470_, lean_object* v_ps_471_, lean_object* v_a_472_, lean_object* v_b_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg(v_upperBound_470_, v_ps_471_, v_a_472_, v_b_473_, v___y_474_);
lean_dec_ref(v_ps_471_);
lean_dec(v_upperBound_470_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go(lean_object* v_ps_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v_snd_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
v___x_478_ = lean_array_get_size(v_ps_476_);
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = lean_box(0);
v___x_481_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg(v___x_478_, v_ps_476_, v___x_479_, v___x_480_, v_a_477_);
v_snd_482_ = lean_ctor_get(v___x_481_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; 
v_unused_490_ = lean_ctor_get(v___x_481_, 0);
lean_dec(v_unused_490_);
v___x_484_ = v___x_481_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_snd_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_480_);
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_480_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_snd_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go___boxed(lean_object* v_ps_491_, lean_object* v_a_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go(v_ps_491_, v_a_492_);
lean_dec_ref(v_ps_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0(lean_object* v_upperBound_494_, lean_object* v_ps_495_, lean_object* v_inst_496_, lean_object* v_R_497_, lean_object* v_a_498_, lean_object* v_b_499_, lean_object* v_c_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___redArg(v_upperBound_494_, v_ps_495_, v_a_498_, v_b_499_, v___y_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0___boxed(lean_object* v_upperBound_503_, lean_object* v_ps_504_, lean_object* v_inst_505_, lean_object* v_R_506_, lean_object* v_a_507_, lean_object* v_b_508_, lean_object* v_c_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go_spec__0(v_upperBound_503_, v_ps_504_, v_inst_505_, v_R_506_, v_a_507_, v_b_508_, v_c_509_, v___y_510_);
lean_dec_ref(v_ps_504_);
lean_dec(v_upperBound_503_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PullFunDecls_attach_spec__0(size_t v_sz_512_, size_t v_i_513_, lean_object* v_bs_514_){
_start:
{
uint8_t v___x_515_; 
v___x_515_ = lean_usize_dec_lt(v_i_513_, v_sz_512_);
if (v___x_515_ == 0)
{
return v_bs_514_;
}
else
{
lean_object* v___x_516_; lean_object* v_bs_x27_517_; uint8_t v___x_518_; size_t v___x_519_; size_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_516_ = lean_unsigned_to_nat(0u);
v_bs_x27_517_ = lean_array_uset(v_bs_514_, v_i_513_, v___x_516_);
v___x_518_ = 0;
v___x_519_ = ((size_t)1ULL);
v___x_520_ = lean_usize_add(v_i_513_, v___x_519_);
v___x_521_ = lean_box(v___x_518_);
v___x_522_ = lean_array_uset(v_bs_x27_517_, v_i_513_, v___x_521_);
v_i_513_ = v___x_520_;
v_bs_514_ = v___x_522_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PullFunDecls_attach_spec__0___boxed(lean_object* v_sz_524_, lean_object* v_i_525_, lean_object* v_bs_526_){
_start:
{
size_t v_sz_boxed_527_; size_t v_i_boxed_528_; lean_object* v_res_529_; 
v_sz_boxed_527_ = lean_unbox_usize(v_sz_524_);
lean_dec(v_sz_524_);
v_i_boxed_528_ = lean_unbox_usize(v_i_525_);
lean_dec(v_i_525_);
v_res_529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PullFunDecls_attach_spec__0(v_sz_boxed_527_, v_i_boxed_528_, v_bs_526_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attach(lean_object* v_ps_530_, lean_object* v_k_531_){
_start:
{
size_t v_sz_532_; size_t v___x_533_; lean_object* v_visited_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v_snd_537_; lean_object* v_fst_538_; 
v_sz_532_ = lean_array_size(v_ps_530_);
v___x_533_ = ((size_t)0ULL);
lean_inc_ref(v_ps_530_);
v_visited_534_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PullFunDecls_attach_spec__0(v_sz_532_, v___x_533_, v_ps_530_);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v_k_531_);
lean_ctor_set(v___x_535_, 1, v_visited_534_);
v___x_536_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_PullFunDecls_attach_go(v_ps_530_, v___x_535_);
lean_dec_ref(v_ps_530_);
v_snd_537_ = lean_ctor_get(v___x_536_, 1);
lean_inc(v_snd_537_);
lean_dec_ref(v___x_536_);
v_fst_538_ = lean_ctor_get(v_snd_537_, 0);
lean_inc(v_fst_538_);
lean_dec(v_snd_537_);
return v_fst_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg(lean_object* v_fvarId_539_, lean_object* v_k_540_, lean_object* v_a_541_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg(v_fvarId_539_, v_a_541_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_552_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_552_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_552_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_552_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = l_Lean_Compiler_LCNF_PullFunDecls_attach(v_a_544_, v_k_540_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_548_);
v___x_550_ = v___x_546_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec_ref(v_k_540_);
v_a_553_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_543_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_543_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg___boxed(lean_object* v_fvarId_561_, lean_object* v_k_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg(v_fvarId_561_, v_k_562_, v_a_563_);
lean_dec(v_a_563_);
lean_dec(v_fvarId_561_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps(lean_object* v_fvarId_566_, lean_object* v_k_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg(v_fvarId_566_, v_k_567_, v_a_568_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___boxed(lean_object* v_fvarId_575_, lean_object* v_k_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps(v_fvarId_575_, v_k_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
lean_dec(v_fvarId_575_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(lean_object* v_params_584_, lean_object* v_k_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___redArg(v_params_584_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_601_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_601_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_601_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_601_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_597_ = l_Lean_Compiler_LCNF_PullFunDecls_attach(v_a_593_, v_k_585_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_597_);
v___x_599_ = v___x_595_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_dec_ref(v_k_585_);
v_a_602_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_592_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_592_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps___boxed(lean_object* v_params_610_, lean_object* v_k_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(v_params_610_, v_k_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_params_610_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Compiler_LCNF_PullFunDecls_attachJps_spec__1(lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
if (lean_obj_tag(v_a_619_) == 0)
{
lean_object* v___x_621_; 
v___x_621_ = l_List_reverse___redArg(v_a_620_);
return v___x_621_;
}
else
{
lean_object* v_head_622_; lean_object* v_tail_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_634_; 
v_head_622_ = lean_ctor_get(v_a_619_, 0);
v_tail_623_ = lean_ctor_get(v_a_619_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_a_619_);
if (v_isSharedCheck_634_ == 0)
{
v___x_625_ = v_a_619_;
v_isShared_626_ = v_isSharedCheck_634_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_tail_623_);
lean_inc(v_head_622_);
lean_dec(v_a_619_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_634_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
uint8_t v_isFun_627_; uint8_t v___x_628_; 
v_isFun_627_ = lean_ctor_get_uint8(v_head_622_, sizeof(void*)*2);
v___x_628_ = lean_bool_not(v_isFun_627_);
if (v___x_628_ == 0)
{
lean_del_object(v___x_625_);
lean_dec(v_head_622_);
v_a_619_ = v_tail_623_;
goto _start;
}
else
{
lean_object* v___x_631_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v_a_620_);
v___x_631_ = v___x_625_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_head_622_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_a_620_);
v___x_631_ = v_reuseFailAlloc_633_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
v_a_619_ = v_tail_623_;
v_a_620_ = v___x_631_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Compiler_LCNF_PullFunDecls_attachJps_spec__0(lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
if (lean_obj_tag(v_a_635_) == 0)
{
lean_object* v___x_637_; 
v___x_637_ = l_List_reverse___redArg(v_a_636_);
return v___x_637_;
}
else
{
lean_object* v_head_638_; uint8_t v_isFun_639_; 
v_head_638_ = lean_ctor_get(v_a_635_, 0);
v_isFun_639_ = lean_ctor_get_uint8(v_head_638_, sizeof(void*)*2);
if (v_isFun_639_ == 0)
{
lean_object* v_tail_640_; 
v_tail_640_ = lean_ctor_get(v_a_635_, 1);
lean_inc(v_tail_640_);
lean_dec_ref_known(v_a_635_, 2);
v_a_635_ = v_tail_640_;
goto _start;
}
else
{
lean_object* v_tail_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_650_; 
lean_inc(v_head_638_);
v_tail_642_ = lean_ctor_get(v_a_635_, 1);
v_isSharedCheck_650_ = !lean_is_exclusive(v_a_635_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; 
v_unused_651_ = lean_ctor_get(v_a_635_, 0);
lean_dec(v_unused_651_);
v___x_644_ = v_a_635_;
v_isShared_645_ = v_isSharedCheck_650_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_tail_642_);
lean_dec(v_a_635_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_650_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 1, v_a_636_);
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_head_638_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_a_636_);
v___x_647_ = v_reuseFailAlloc_649_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
v_a_635_ = v_tail_642_;
v_a_636_ = v___x_647_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg(lean_object* v_k_652_, lean_object* v_a_653_){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_655_ = lean_st_ref_get(v_a_653_);
v___x_656_ = lean_st_ref_take(v_a_653_);
v___x_657_ = lean_box(0);
v___x_658_ = l_List_filterTR_loop___at___00Lean_Compiler_LCNF_PullFunDecls_attachJps_spec__0(v___x_656_, v___x_657_);
v___x_659_ = lean_st_ref_set(v_a_653_, v___x_658_);
v___x_660_ = l_List_filterTR_loop___at___00Lean_Compiler_LCNF_PullFunDecls_attachJps_spec__1(v___x_655_, v___x_657_);
v___x_661_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___redArg___closed__0));
v___x_662_ = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDepsFixpoint___redArg(v___x_660_, v___x_661_, v_a_653_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_671_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_671_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = l_Lean_Compiler_LCNF_PullFunDecls_attach(v_a_663_, v_k_652_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_667_);
v___x_669_ = v___x_665_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_dec_ref(v_k_652_);
v_a_672_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_662_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_662_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg___boxed(lean_object* v_k_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg(v_k_680_, v_a_681_);
lean_dec(v_a_681_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachJps(lean_object* v_k_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg(v_k_684_, v_a_685_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachJps___boxed(lean_object* v_k_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_Compiler_LCNF_PullFunDecls_attachJps(v_k_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_addToPull(uint8_t v_isFun_700_, lean_object* v_decl_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_params_712_; lean_object* v_type_713_; lean_object* v_value_714_; lean_object* v___x_715_; 
v___x_708_ = lean_st_ref_get(v_a_702_);
v___x_709_ = lean_st_ref_take(v_a_702_);
lean_dec(v___x_709_);
v___x_710_ = lean_box(0);
v___x_711_ = lean_st_ref_set(v_a_702_, v___x_710_);
v_params_712_ = lean_ctor_get(v_decl_701_, 2);
lean_inc_ref(v_params_712_);
v_type_713_ = lean_ctor_get(v_decl_701_, 3);
lean_inc_ref(v_type_713_);
v_value_714_ = lean_ctor_get(v_decl_701_, 4);
lean_inc_ref(v_value_714_);
v___x_715_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(v_value_714_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_717_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_716_);
lean_dec_ref_known(v___x_715_, 1);
v___x_717_ = l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(v_params_712_, v_a_716_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_719_; uint8_t v___x_720_; lean_object* v_value_722_; lean_object* v___y_723_; lean_object* v___y_724_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 1);
v___x_719_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_720_ = 0;
if (v_isFun_700_ == 0)
{
v_value_722_ = v_a_718_;
v___y_723_ = v_a_702_;
v___y_724_ = v_a_704_;
goto v___jp_721_;
}
else
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Compiler_LCNF_PullFunDecls_attachJps___redArg(v_a_718_, v_a_702_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v___x_749_, 1);
v_value_722_ = v_a_750_;
v___y_723_ = v_a_702_;
v___y_724_ = v_a_704_;
goto v___jp_721_;
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec_ref(v_type_713_);
lean_dec_ref(v_params_712_);
lean_dec(v___x_708_);
lean_dec_ref(v_decl_701_);
v_a_751_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_749_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_749_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
v___jp_721_:
{
lean_object* v___x_725_; 
v___x_725_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_720_, v_decl_701_, v_type_713_, v_params_712_, v_value_722_, v___y_724_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_740_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_740_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_740_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_740_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
v___x_730_ = lean_st_ref_take(v___y_723_);
lean_inc(v_a_726_);
v___x_731_ = l_Lean_Compiler_LCNF_FunDecl_collectUsed(v___x_720_, v_a_726_, v___x_719_);
v___x_732_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_732_, 0, v_a_726_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
lean_ctor_set_uint8(v___x_732_, sizeof(void*)*2, v_isFun_700_);
v___x_733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v___x_730_);
v___x_734_ = l_List_appendTR___redArg(v___x_733_, v___x_708_);
v___x_735_ = lean_st_ref_set(v___y_723_, v___x_734_);
v___x_736_ = lean_box(0);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_736_);
v___x_738_ = v___x_728_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v___x_708_);
v_a_741_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_725_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_725_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec_ref(v_type_713_);
lean_dec_ref(v_params_712_);
lean_dec(v___x_708_);
lean_dec_ref(v_decl_701_);
v_a_759_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_717_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_717_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec_ref(v_type_713_);
lean_dec_ref(v_params_712_);
lean_dec(v___x_708_);
lean_dec_ref(v_decl_701_);
v_a_767_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_715_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_715_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_pull(lean_object* v_code_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
switch(lean_obj_tag(v_code_775_))
{
case 0:
{
lean_object* v_decl_782_; lean_object* v_k_783_; lean_object* v___x_784_; 
v_decl_782_ = lean_ctor_get(v_code_775_, 0);
v_k_783_ = lean_ctor_get(v_code_775_, 1);
lean_inc_ref(v_k_783_);
v___x_784_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(v_k_783_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v_fvarId_786_; lean_object* v___x_787_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref_known(v___x_784_, 1);
v_fvarId_786_ = lean_ctor_get(v_decl_782_, 0);
v___x_787_ = l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps___redArg(v_fvarId_786_, v_a_785_, v_a_776_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_814_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_814_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_814_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_814_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
uint8_t v___y_793_; size_t v___x_809_; size_t v___x_810_; uint8_t v___x_811_; 
v___x_809_ = lean_ptr_addr(v_k_783_);
v___x_810_ = lean_ptr_addr(v_a_788_);
v___x_811_ = lean_usize_dec_eq(v___x_809_, v___x_810_);
if (v___x_811_ == 0)
{
v___y_793_ = v___x_811_;
goto v___jp_792_;
}
else
{
size_t v___x_812_; uint8_t v___x_813_; 
v___x_812_ = lean_ptr_addr(v_decl_782_);
v___x_813_ = lean_usize_dec_eq(v___x_812_, v___x_812_);
v___y_793_ = v___x_813_;
goto v___jp_792_;
}
v___jp_792_:
{
if (v___y_793_ == 0)
{
lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_803_; 
lean_inc_ref(v_decl_782_);
v_isSharedCheck_803_ = !lean_is_exclusive(v_code_775_);
if (v_isSharedCheck_803_ == 0)
{
lean_object* v_unused_804_; lean_object* v_unused_805_; 
v_unused_804_ = lean_ctor_get(v_code_775_, 1);
lean_dec(v_unused_804_);
v_unused_805_ = lean_ctor_get(v_code_775_, 0);
lean_dec(v_unused_805_);
v___x_795_ = v_code_775_;
v_isShared_796_ = v_isSharedCheck_803_;
goto v_resetjp_794_;
}
else
{
lean_dec(v_code_775_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_803_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v_a_788_);
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_decl_782_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_a_788_);
v___x_798_ = v_reuseFailAlloc_802_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_800_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_798_);
v___x_800_ = v___x_790_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
else
{
lean_object* v___x_807_; 
lean_dec(v_a_788_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v_code_775_);
v___x_807_ = v___x_790_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_code_775_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_775_, 2);
return v___x_787_;
}
}
else
{
lean_dec_ref_known(v_code_775_, 2);
return v___x_784_;
}
}
case 1:
{
lean_object* v_decl_815_; lean_object* v_k_816_; uint8_t v___x_817_; lean_object* v___x_818_; 
v_decl_815_ = lean_ctor_get(v_code_775_, 0);
lean_inc_ref(v_decl_815_);
v_k_816_ = lean_ctor_get(v_code_775_, 1);
lean_inc_ref(v_k_816_);
lean_dec_ref_known(v_code_775_, 2);
v___x_817_ = 1;
v___x_818_ = l_Lean_Compiler_LCNF_PullFunDecls_addToPull(v___x_817_, v_decl_815_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_dec_ref_known(v___x_818_, 1);
v_code_775_ = v_k_816_;
goto _start;
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec_ref(v_k_816_);
v_a_820_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_818_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_818_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
case 2:
{
lean_object* v_decl_828_; lean_object* v_k_829_; uint8_t v___x_830_; lean_object* v___x_831_; 
v_decl_828_ = lean_ctor_get(v_code_775_, 0);
lean_inc_ref(v_decl_828_);
v_k_829_ = lean_ctor_get(v_code_775_, 1);
lean_inc_ref(v_k_829_);
lean_dec_ref_known(v_code_775_, 2);
v___x_830_ = 0;
v___x_831_ = l_Lean_Compiler_LCNF_PullFunDecls_addToPull(v___x_830_, v_decl_828_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_dec_ref_known(v___x_831_, 1);
v_code_775_ = v_k_829_;
goto _start;
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec_ref(v_k_829_);
v_a_833_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_831_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_831_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
case 4:
{
lean_object* v_cases_841_; lean_object* v_typeName_842_; lean_object* v_resultType_843_; lean_object* v_discr_844_; lean_object* v_alts_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_884_; 
v_cases_841_ = lean_ctor_get(v_code_775_, 0);
lean_inc_ref(v_cases_841_);
v_typeName_842_ = lean_ctor_get(v_cases_841_, 0);
v_resultType_843_ = lean_ctor_get(v_cases_841_, 1);
v_discr_844_ = lean_ctor_get(v_cases_841_, 2);
v_alts_845_ = lean_ctor_get(v_cases_841_, 3);
v_isSharedCheck_884_ = !lean_is_exclusive(v_cases_841_);
if (v_isSharedCheck_884_ == 0)
{
v___x_847_ = v_cases_841_;
v_isShared_848_ = v_isSharedCheck_884_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_alts_845_);
lean_inc(v_discr_844_);
lean_inc(v_resultType_843_);
lean_inc(v_typeName_842_);
lean_dec(v_cases_841_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_884_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_845_);
v___x_850_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullFunDecls_pull_spec__1(v___x_849_, v_alts_845_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_875_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_875_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_875_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_875_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
size_t v___x_855_; size_t v___x_856_; uint8_t v___x_857_; 
v___x_855_ = lean_ptr_addr(v_alts_845_);
lean_dec_ref(v_alts_845_);
v___x_856_ = lean_ptr_addr(v_a_851_);
v___x_857_ = lean_usize_dec_eq(v___x_855_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_870_; 
v_isSharedCheck_870_ = !lean_is_exclusive(v_code_775_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; 
v_unused_871_ = lean_ctor_get(v_code_775_, 0);
lean_dec(v_unused_871_);
v___x_859_ = v_code_775_;
v_isShared_860_ = v_isSharedCheck_870_;
goto v_resetjp_858_;
}
else
{
lean_dec(v_code_775_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_870_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 3, v_a_851_);
v___x_862_ = v___x_847_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_typeName_842_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_resultType_843_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v_discr_844_);
lean_ctor_set(v_reuseFailAlloc_869_, 3, v_a_851_);
v___x_862_ = v_reuseFailAlloc_869_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_864_; 
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_862_);
v___x_864_ = v___x_859_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_862_);
v___x_864_ = v_reuseFailAlloc_868_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_866_; 
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_864_);
v___x_866_ = v___x_853_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
else
{
lean_object* v___x_873_; 
lean_dec(v_a_851_);
lean_del_object(v___x_847_);
lean_dec(v_discr_844_);
lean_dec_ref(v_resultType_843_);
lean_dec(v_typeName_842_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v_code_775_);
v___x_873_ = v___x_853_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_code_775_);
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
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_del_object(v___x_847_);
lean_dec_ref(v_alts_845_);
lean_dec(v_discr_844_);
lean_dec_ref(v_resultType_843_);
lean_dec(v_typeName_842_);
lean_dec_ref_known(v_code_775_, 1);
v_a_876_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_850_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_850_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
default: 
{
lean_object* v___x_885_; 
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v_code_775_);
return v___x_885_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullFunDecls_pull_spec__1(lean_object* v_i_886_, lean_object* v_as_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_894_ = lean_array_get_size(v_as_887_);
v___x_895_ = lean_nat_dec_lt(v_i_886_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
lean_dec(v_i_886_);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v_as_887_);
return v___x_896_;
}
else
{
lean_object* v_a_897_; lean_object* v_a_899_; 
v_a_897_ = lean_array_fget_borrowed(v_as_887_, v_i_886_);
if (lean_obj_tag(v_a_897_) == 0)
{
lean_object* v_params_910_; lean_object* v_code_911_; lean_object* v___x_912_; 
v_params_910_ = lean_ctor_get(v_a_897_, 1);
v_code_911_ = lean_ctor_get(v_a_897_, 2);
lean_inc_ref(v_code_911_);
v___x_912_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(v_code_911_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_914_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(v_params_910_, v_a_913_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_916_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v___x_914_, 1);
lean_inc_ref(v_a_897_);
v___x_916_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_897_, v_a_915_);
v_a_899_ = v___x_916_;
goto v___jp_898_;
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec_ref(v_as_887_);
lean_dec(v_i_886_);
v_a_917_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_914_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_914_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v_as_887_);
lean_dec(v_i_886_);
v_a_925_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_912_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_912_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
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
lean_object* v_code_933_; lean_object* v___x_934_; 
v_code_933_ = lean_ctor_get(v_a_897_, 0);
lean_inc_ref(v_code_933_);
v___x_934_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(v_code_933_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_936_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
lean_dec_ref_known(v___x_934_, 1);
lean_inc_ref(v_a_897_);
v___x_936_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_897_, v_a_935_);
v_a_899_ = v___x_936_;
goto v___jp_898_;
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v_as_887_);
lean_dec(v_i_886_);
v_a_937_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_934_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_934_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
v___jp_898_:
{
size_t v___x_900_; size_t v___x_901_; uint8_t v___x_902_; 
v___x_900_ = lean_ptr_addr(v_a_897_);
v___x_901_ = lean_ptr_addr(v_a_899_);
v___x_902_ = lean_usize_dec_eq(v___x_900_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = lean_unsigned_to_nat(1u);
v___x_904_ = lean_nat_add(v_i_886_, v___x_903_);
v___x_905_ = lean_array_fset(v_as_887_, v_i_886_, v_a_899_);
lean_dec(v_i_886_);
v_i_886_ = v___x_904_;
v_as_887_ = v___x_905_;
goto _start;
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; 
lean_dec_ref(v_a_899_);
v___x_907_ = lean_unsigned_to_nat(1u);
v___x_908_ = lean_nat_add(v_i_886_, v___x_907_);
lean_dec(v_i_886_);
v_i_886_ = v___x_908_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullFunDecls_pull_spec__1___boxed(lean_object* v_i_945_, lean_object* v_as_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullFunDecls_pull_spec__1(v_i_945_, v_as_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_addToPull___boxed(lean_object* v_isFun_954_, lean_object* v_decl_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
uint8_t v_isFun_boxed_962_; lean_object* v_res_963_; 
v_isFun_boxed_962_ = lean_unbox(v_isFun_954_);
v_res_963_ = l_Lean_Compiler_LCNF_PullFunDecls_addToPull(v_isFun_boxed_962_, v_decl_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_pull___boxed(lean_object* v_code_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_Compiler_LCNF_PullFunDecls_pull(v_code_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_);
lean_dec(v_a_969_);
lean_dec_ref(v_a_968_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec(v_a_965_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg(lean_object* v_f_972_, lean_object* v_v_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
if (lean_obj_tag(v_v_973_) == 0)
{
lean_object* v_code_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1004_; 
v_code_980_ = lean_ctor_get(v_v_973_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_v_973_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_982_ = v_v_973_;
v_isShared_983_ = v_isSharedCheck_1004_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_code_980_);
lean_dec(v_v_973_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1004_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; 
lean_inc(v___y_978_);
lean_inc_ref(v___y_977_);
lean_inc(v___y_976_);
lean_inc_ref(v___y_975_);
lean_inc(v___y_974_);
v___x_984_ = lean_apply_7(v_f_972_, v_code_980_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, lean_box(0));
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_995_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_995_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_995_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_995_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v_a_985_);
v___x_990_ = v___x_982_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_994_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_992_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_990_);
v___x_992_ = v___x_987_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_del_object(v___x_982_);
v_a_996_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_984_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_984_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
else
{
lean_object* v___x_1005_; 
lean_dec_ref(v_f_972_);
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v_v_973_);
return v___x_1005_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg___boxed(lean_object* v_f_1006_, lean_object* v_v_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg(v_f_1006_, v_v_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0(uint8_t v_pu_1015_, lean_object* v_f_1016_, lean_object* v_v_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg(v_f_1016_, v_v_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___boxed(lean_object* v_pu_1025_, lean_object* v_f_1026_, lean_object* v_v_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
uint8_t v_pu_boxed_1034_; lean_object* v_res_1035_; 
v_pu_boxed_1034_ = lean_unbox(v_pu_1025_);
v_res_1035_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0(v_pu_boxed_1034_, v_f_1026_, v_v_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullFunDecls(lean_object* v_decl_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v_toSignature_1045_; lean_object* v_value_1046_; uint8_t v_recursive_1047_; lean_object* v_inlineAttr_x3f_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1077_; 
v___x_1043_ = lean_box(0);
v___x_1044_ = lean_st_mk_ref(v___x_1043_);
v_toSignature_1045_ = lean_ctor_get(v_decl_1037_, 0);
v_value_1046_ = lean_ctor_get(v_decl_1037_, 1);
v_recursive_1047_ = lean_ctor_get_uint8(v_decl_1037_, sizeof(void*)*3);
v_inlineAttr_x3f_1048_ = lean_ctor_get(v_decl_1037_, 2);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_decl_1037_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1050_ = v_decl_1037_;
v_isShared_1051_ = v_isSharedCheck_1077_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_inlineAttr_x3f_1048_);
lean_inc(v_value_1046_);
lean_inc(v_toSignature_1045_);
lean_dec(v_decl_1037_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1077_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_pullFunDecls___closed__0));
v___x_1053_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullFunDecls_spec__0___redArg(v___x_1052_, v_value_1046_, v___x_1044_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1068_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1056_ = v___x_1053_;
v_isShared_1057_ = v_isSharedCheck_1068_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1068_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1058_ = lean_st_ref_get(v___x_1044_);
lean_dec(v___x_1044_);
v___x_1059_ = lean_array_mk(v___x_1058_);
v___x_1060_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PullFunDecls_attach), 2, 1);
lean_closure_set(v___x_1060_, 0, v___x_1059_);
v___x_1061_ = l_Lean_Compiler_LCNF_DeclValue_mapCode___redArg(v___x_1060_, v_a_1054_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v___x_1061_);
v___x_1063_ = v___x_1050_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_toSignature_1045_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v___x_1061_);
lean_ctor_set(v_reuseFailAlloc_1067_, 2, v_inlineAttr_x3f_1048_);
lean_ctor_set_uint8(v_reuseFailAlloc_1067_, sizeof(void*)*3, v_recursive_1047_);
v___x_1063_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1065_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1063_);
v___x_1065_ = v___x_1056_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1063_);
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
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_del_object(v___x_1050_);
lean_dec(v_inlineAttr_x3f_1048_);
lean_dec_ref(v_toSignature_1045_);
lean_dec(v___x_1044_);
v_a_1069_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1053_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1053_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullFunDecls___boxed(lean_object* v_decl_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_Compiler_LCNF_Decl_pullFunDecls(v_decl_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
return v_res_1084_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullFunDecls___closed__3(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1089_ = lean_unsigned_to_nat(0u);
v___x_1090_ = ((lean_object*)(l_Lean_Compiler_LCNF_pullFunDecls___closed__2));
v___x_1091_ = 0;
v___x_1092_ = ((lean_object*)(l_Lean_Compiler_LCNF_pullFunDecls___closed__1));
v___x_1093_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1092_, v___x_1091_, v___x_1090_, v___x_1089_);
return v___x_1093_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullFunDecls(void){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_obj_once(&l_Lean_Compiler_LCNF_pullFunDecls___closed__3, &l_Lean_Compiler_LCNF_pullFunDecls___closed__3_once, _init_l_Lean_Compiler_LCNF_pullFunDecls___closed__3);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1165_; uint8_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1165_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_));
v___x_1166_ = 1;
v___x_1167_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_));
v___x_1168_ = l_Lean_registerTraceClass(v___x_1165_, v___x_1166_, v___x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2____boxed(lean_object* v_a_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l___private_Lean_Compiler_LCNF_PullFunDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullFunDecls_1553090079____hygCtx___hyg_2_();
return v_res_1170_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_PullFunDecls(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
