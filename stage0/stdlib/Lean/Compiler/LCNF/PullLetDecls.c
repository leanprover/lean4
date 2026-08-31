// Lean compiler output
// Module: Lean.Compiler.LCNF.PullLetDecls
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
lean_object* l_Lean_Compiler_LCNF_isClass_x3f___redArg(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(uint8_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withFVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__3_value;
static const lean_closure_object l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__4_value;
static const lean_closure_object l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__5_value;
static const lean_closure_object l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__0_value),((lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__1_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__7_value),((lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__3_value),((lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__4_value),((lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__5_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__8_value),((lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__6_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__9_value;
static const lean_closure_object l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withNewScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withNewScope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withNewScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withNewScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_PullLetDecls_withCheckpoint_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_PullLetDecls_withCheckpoint_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_attachToPull_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_attachToPull_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_attachToPull___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_attachToPull___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_attachToPull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_attachToPull___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_shouldPull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_shouldPull___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2(lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp"};
static const lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_PullM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_PullLetDecls_attachToPull___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Decl_pullLetDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_pullLetDecls___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullInstances___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullInstances___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Decl_pullInstances___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Decl_pullInstances___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Decl_pullInstances___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_pullInstances___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_pullInstances___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "pullInstances"};
static const lean_object* l_Lean_Compiler_LCNF_pullInstances___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_pullInstances___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_pullInstances___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_pullInstances___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 64, 178, 67, 149, 31, 237, 171)}};
static const lean_object* l_Lean_Compiler_LCNF_pullInstances___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_pullInstances___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_pullInstances___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Decl_pullInstances___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_pullInstances___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_pullInstances___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_pullInstances___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_pullInstances___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_pullInstances;
static const lean_string_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_pullInstances___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 201, 254, 145, 100, 42, 166, 160)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PullLetDecls"};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(27, 241, 159, 200, 135, 109, 225, 185)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(166, 136, 187, 86, 18, 25, 137, 250)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 251, 46, 178, 152, 200, 229, 229)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 158, 200, 255, 227, 47, 35, 179)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(132, 194, 125, 228, 235, 98, 41, 196)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 133, 224, 244, 214, 86, 90, 84)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(108, 69, 254, 167, 12, 16, 110, 124)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(109, 16, 148, 33, 118, 65, 200, 4)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(11, 149, 17, 125, 174, 166, 104, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(182, 72, 13, 30, 160, 214, 147, 68)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 189, 197, 199, 72, 35, 203, 245)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withFVar___redArg(lean_object* v_fvarId_1_, lean_object* v_x_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v_isCandidateFn_10_; lean_object* v_included_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_isCandidateFn_10_ = lean_ctor_get(v_a_3_, 0);
v_included_11_ = lean_ctor_get(v_a_3_, 1);
lean_inc(v_included_11_);
v___x_12_ = l_Lean_FVarIdSet_insert(v_included_11_, v_fvarId_1_);
lean_inc_ref(v_isCandidateFn_10_);
v___x_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_13_, 0, v_isCandidateFn_10_);
lean_ctor_set(v___x_13_, 1, v___x_12_);
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
v___x_14_ = lean_apply_7(v_x_2_, v___x_13_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withFVar___redArg___boxed(lean_object* v_fvarId_15_, lean_object* v_x_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Compiler_LCNF_PullLetDecls_withFVar___redArg(v_fvarId_15_, v_x_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_);
lean_dec(v_a_22_);
lean_dec_ref(v_a_21_);
lean_dec(v_a_20_);
lean_dec_ref(v_a_19_);
lean_dec(v_a_18_);
lean_dec_ref(v_a_17_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withFVar(lean_object* v_00_u03b1_25_, lean_object* v_fvarId_26_, lean_object* v_x_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_isCandidateFn_35_; lean_object* v_included_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v_isCandidateFn_35_ = lean_ctor_get(v_a_28_, 0);
v_included_36_ = lean_ctor_get(v_a_28_, 1);
lean_inc(v_included_36_);
v___x_37_ = l_Lean_FVarIdSet_insert(v_included_36_, v_fvarId_26_);
lean_inc_ref(v_isCandidateFn_35_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v_isCandidateFn_35_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
lean_inc(v_a_33_);
lean_inc_ref(v_a_32_);
lean_inc(v_a_31_);
lean_inc_ref(v_a_30_);
lean_inc(v_a_29_);
v___x_39_ = lean_apply_7(v_x_27_, v___x_38_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, lean_box(0));
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withFVar___boxed(lean_object* v_00_u03b1_40_, lean_object* v_fvarId_41_, lean_object* v_x_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Compiler_LCNF_PullLetDecls_withFVar(v_00_u03b1_40_, v_fvarId_41_, v_x_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
lean_dec(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec(v_a_46_);
lean_dec_ref(v_a_45_);
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___lam__0(lean_object* v_x1_51_, lean_object* v_x2_52_){
_start:
{
lean_object* v_fvarId_53_; lean_object* v___x_54_; 
v_fvarId_53_ = lean_ctor_get(v_x2_52_, 0);
lean_inc(v_fvarId_53_);
lean_dec_ref(v_x2_52_);
v___x_54_ = l_Lean_FVarIdSet_insert(v_x1_51_, v_fvarId_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg(lean_object* v_ps_75_, lean_object* v_x_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_isCandidateFn_84_; lean_object* v_included_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v_isCandidateFn_84_ = lean_ctor_get(v_a_77_, 0);
v_included_85_ = lean_ctor_get(v_a_77_, 1);
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = lean_array_get_size(v_ps_75_);
v___x_88_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__9));
v___x_89_ = lean_nat_dec_lt(v___x_86_, v___x_87_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
lean_dec_ref(v_ps_75_);
lean_inc(v_a_82_);
lean_inc_ref(v_a_81_);
lean_inc(v_a_80_);
lean_inc_ref(v_a_79_);
lean_inc(v_a_78_);
lean_inc_ref(v_a_77_);
v___x_90_ = lean_apply_7(v_x_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, lean_box(0));
return v___x_90_;
}
else
{
lean_object* v___f_91_; uint8_t v___x_92_; 
v___f_91_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__10));
v___x_92_ = lean_nat_dec_le(v___x_87_, v___x_87_);
if (v___x_92_ == 0)
{
if (v___x_89_ == 0)
{
lean_object* v___x_93_; 
lean_dec_ref(v_ps_75_);
lean_inc(v_a_82_);
lean_inc_ref(v_a_81_);
lean_inc(v_a_80_);
lean_inc_ref(v_a_79_);
lean_inc(v_a_78_);
lean_inc_ref(v_a_77_);
v___x_93_ = lean_apply_7(v_x_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, lean_box(0));
return v___x_93_;
}
else
{
size_t v___x_94_; size_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_94_ = ((size_t)0ULL);
v___x_95_ = lean_usize_of_nat(v___x_87_);
lean_inc(v_included_85_);
v___x_96_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_88_, v___f_91_, v_ps_75_, v___x_94_, v___x_95_, v_included_85_);
lean_inc_ref(v_isCandidateFn_84_);
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v_isCandidateFn_84_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
lean_inc(v_a_82_);
lean_inc_ref(v_a_81_);
lean_inc(v_a_80_);
lean_inc_ref(v_a_79_);
lean_inc(v_a_78_);
v___x_98_ = lean_apply_7(v_x_76_, v___x_97_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, lean_box(0));
return v___x_98_;
}
}
else
{
size_t v___x_99_; size_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_99_ = ((size_t)0ULL);
v___x_100_ = lean_usize_of_nat(v___x_87_);
lean_inc(v_included_85_);
v___x_101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_88_, v___f_91_, v_ps_75_, v___x_99_, v___x_100_, v_included_85_);
lean_inc_ref(v_isCandidateFn_84_);
v___x_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_102_, 0, v_isCandidateFn_84_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
lean_inc(v_a_82_);
lean_inc_ref(v_a_81_);
lean_inc(v_a_80_);
lean_inc_ref(v_a_79_);
lean_inc(v_a_78_);
v___x_103_ = lean_apply_7(v_x_76_, v___x_102_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, lean_box(0));
return v___x_103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___boxed(lean_object* v_ps_104_, lean_object* v_x_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg(v_ps_104_, v_x_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams(lean_object* v_00_u03b1_114_, lean_object* v_ps_115_, lean_object* v_x_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v_isCandidateFn_124_; lean_object* v_included_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v_isCandidateFn_124_ = lean_ctor_get(v_a_117_, 0);
v_included_125_ = lean_ctor_get(v_a_117_, 1);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_array_get_size(v_ps_115_);
v___x_128_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__9));
v___x_129_ = lean_nat_dec_lt(v___x_126_, v___x_127_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; 
lean_dec_ref(v_ps_115_);
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
lean_inc(v_a_120_);
lean_inc_ref(v_a_119_);
lean_inc(v_a_118_);
lean_inc_ref(v_a_117_);
v___x_130_ = lean_apply_7(v_x_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, lean_box(0));
return v___x_130_;
}
else
{
lean_object* v___f_131_; uint8_t v___x_132_; 
v___f_131_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__10));
v___x_132_ = lean_nat_dec_le(v___x_127_, v___x_127_);
if (v___x_132_ == 0)
{
if (v___x_129_ == 0)
{
lean_object* v___x_133_; 
lean_dec_ref(v_ps_115_);
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
lean_inc(v_a_120_);
lean_inc_ref(v_a_119_);
lean_inc(v_a_118_);
lean_inc_ref(v_a_117_);
v___x_133_ = lean_apply_7(v_x_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, lean_box(0));
return v___x_133_;
}
else
{
size_t v___x_134_; size_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_134_ = ((size_t)0ULL);
v___x_135_ = lean_usize_of_nat(v___x_127_);
lean_inc(v_included_125_);
v___x_136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_128_, v___f_131_, v_ps_115_, v___x_134_, v___x_135_, v_included_125_);
lean_inc_ref(v_isCandidateFn_124_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v_isCandidateFn_124_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
lean_inc(v_a_120_);
lean_inc_ref(v_a_119_);
lean_inc(v_a_118_);
v___x_138_ = lean_apply_7(v_x_116_, v___x_137_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, lean_box(0));
return v___x_138_;
}
}
else
{
size_t v___x_139_; size_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_139_ = ((size_t)0ULL);
v___x_140_ = lean_usize_of_nat(v___x_127_);
lean_inc(v_included_125_);
v___x_141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_128_, v___f_131_, v_ps_115_, v___x_139_, v___x_140_, v_included_125_);
lean_inc_ref(v_isCandidateFn_124_);
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v_isCandidateFn_124_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
lean_inc(v_a_120_);
lean_inc_ref(v_a_119_);
lean_inc(v_a_118_);
v___x_143_ = lean_apply_7(v_x_116_, v___x_142_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, lean_box(0));
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___boxed(lean_object* v_00_u03b1_144_, lean_object* v_ps_145_, lean_object* v_x_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Compiler_LCNF_PullLetDecls_withParams(v_00_u03b1_144_, v_ps_145_, v_x_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withNewScope___redArg(lean_object* v_x_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_isCandidateFn_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_isCandidateFn_163_ = lean_ctor_get(v_a_156_, 0);
v___x_164_ = lean_box(1);
lean_inc_ref(v_isCandidateFn_163_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v_isCandidateFn_163_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
lean_inc(v_a_161_);
lean_inc_ref(v_a_160_);
lean_inc(v_a_159_);
lean_inc_ref(v_a_158_);
lean_inc(v_a_157_);
v___x_166_ = lean_apply_7(v_x_155_, v___x_165_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, lean_box(0));
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withNewScope___redArg___boxed(lean_object* v_x_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Compiler_LCNF_PullLetDecls_withNewScope___redArg(v_x_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withNewScope(lean_object* v_00_u03b1_176_, lean_object* v_x_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_isCandidateFn_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_isCandidateFn_185_ = lean_ctor_get(v_a_178_, 0);
v___x_186_ = lean_box(1);
lean_inc_ref(v_isCandidateFn_185_);
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v_isCandidateFn_185_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
lean_inc(v_a_183_);
lean_inc_ref(v_a_182_);
lean_inc(v_a_181_);
lean_inc_ref(v_a_180_);
lean_inc(v_a_179_);
v___x_188_ = lean_apply_7(v_x_177_, v___x_187_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, lean_box(0));
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withNewScope___boxed(lean_object* v_00_u03b1_189_, lean_object* v_x_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_Compiler_LCNF_PullLetDecls_withNewScope(v_00_u03b1_189_, v_x_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_PullLetDecls_withCheckpoint_go(lean_object* v_c_199_, lean_object* v_toPull_200_, lean_object* v_i_201_, lean_object* v_included_202_, lean_object* v_a_203_){
_start:
{
lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_204_ = lean_array_get_size(v_toPull_200_);
v___x_205_ = lean_nat_dec_lt(v_i_201_, v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
lean_dec(v_included_202_);
lean_dec(v_i_201_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v_c_199_);
lean_ctor_set(v___x_206_, 1, v_a_203_);
return v___x_206_;
}
else
{
lean_object* v_letDecl_207_; uint8_t v___x_208_; uint8_t v___x_209_; 
v_letDecl_207_ = lean_array_fget_borrowed(v_toPull_200_, v_i_201_);
v___x_208_ = 0;
v___x_209_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v___x_208_, v_letDecl_207_, v_included_202_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
lean_inc(v_letDecl_207_);
v___x_210_ = lean_array_push(v_a_203_, v_letDecl_207_);
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_add(v_i_201_, v___x_211_);
lean_dec(v_i_201_);
v_i_201_ = v___x_212_;
v_a_203_ = v___x_210_;
goto _start;
}
else
{
lean_object* v_fvarId_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v_fst_219_; lean_object* v_snd_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_228_; 
v_fvarId_214_ = lean_ctor_get(v_letDecl_207_, 0);
v___x_215_ = lean_unsigned_to_nat(1u);
v___x_216_ = lean_nat_add(v_i_201_, v___x_215_);
lean_dec(v_i_201_);
lean_inc(v_fvarId_214_);
v___x_217_ = l_Lean_FVarIdSet_insert(v_included_202_, v_fvarId_214_);
v___x_218_ = l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_PullLetDecls_withCheckpoint_go(v_c_199_, v_toPull_200_, v___x_216_, v___x_217_, v_a_203_);
v_fst_219_ = lean_ctor_get(v___x_218_, 0);
v_snd_220_ = lean_ctor_get(v___x_218_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_228_ == 0)
{
v___x_222_ = v___x_218_;
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_snd_220_);
lean_inc(v_fst_219_);
lean_dec(v___x_218_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_226_; 
lean_inc(v_letDecl_207_);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v_letDecl_207_);
lean_ctor_set(v___x_224_, 1, v_fst_219_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v___x_224_);
v___x_226_ = v___x_222_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_snd_220_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_PullLetDecls_withCheckpoint_go___boxed(lean_object* v_c_229_, lean_object* v_toPull_230_, lean_object* v_i_231_, lean_object* v_included_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_PullLetDecls_withCheckpoint_go(v_c_229_, v_toPull_230_, v_i_231_, v_included_232_, v_a_233_);
lean_dec_ref(v_toPull_230_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint(lean_object* v_x_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v___x_245_; lean_object* v_isCandidateFn_246_; lean_object* v_included_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_245_ = lean_st_ref_get(v_a_239_);
v_isCandidateFn_246_ = lean_ctor_get(v_a_238_, 0);
v_included_247_ = lean_ctor_get(v_a_238_, 1);
v___x_248_ = lean_box(1);
lean_inc_ref(v_isCandidateFn_246_);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v_isCandidateFn_246_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
lean_inc(v_a_243_);
lean_inc_ref(v_a_242_);
lean_inc(v_a_241_);
lean_inc_ref(v_a_240_);
lean_inc(v_a_239_);
v___x_250_ = lean_apply_7(v_x_237_, v___x_249_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, lean_box(0));
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_268_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_268_ == 0)
{
v___x_253_ = v___x_250_;
v_isShared_254_ = v_isSharedCheck_268_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_268_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v_fst_259_; lean_object* v_snd_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_255_ = lean_st_ref_get(v_a_239_);
v___x_256_ = lean_array_get_size(v___x_245_);
lean_dec(v___x_245_);
v___x_257_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint___closed__0));
lean_inc(v_included_247_);
v___x_258_ = l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_PullLetDecls_withCheckpoint_go(v_a_251_, v___x_255_, v___x_256_, v_included_247_, v___x_257_);
lean_dec(v___x_255_);
v_fst_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_fst_259_);
v_snd_260_ = lean_ctor_get(v___x_258_, 1);
lean_inc(v_snd_260_);
lean_dec_ref(v___x_258_);
v___x_261_ = lean_st_ref_take(v_a_239_);
v___x_262_ = l_Array_shrink___redArg(v___x_261_, v___x_256_);
v___x_263_ = l_Array_append___redArg(v___x_262_, v_snd_260_);
lean_dec(v_snd_260_);
v___x_264_ = lean_st_ref_put(v_a_239_, v___x_263_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v_fst_259_);
v___x_266_ = v___x_253_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_fst_259_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
else
{
lean_dec(v___x_245_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint___boxed(lean_object* v_x_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint(v_x_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
lean_dec(v_a_271_);
lean_dec_ref(v_a_270_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_attachToPull_spec__0(lean_object* v_as_278_, size_t v_i_279_, size_t v_stop_280_, lean_object* v_b_281_){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = lean_usize_dec_eq(v_i_279_, v_stop_280_);
if (v___x_282_ == 0)
{
size_t v___x_283_; size_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_283_ = ((size_t)1ULL);
v___x_284_ = lean_usize_sub(v_i_279_, v___x_283_);
v___x_285_ = lean_array_uget_borrowed(v_as_278_, v___x_284_);
lean_inc(v___x_285_);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v_b_281_);
v_i_279_ = v___x_284_;
v_b_281_ = v___x_286_;
goto _start;
}
else
{
return v_b_281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_attachToPull_spec__0___boxed(lean_object* v_as_288_, lean_object* v_i_289_, lean_object* v_stop_290_, lean_object* v_b_291_){
_start:
{
size_t v_i_boxed_292_; size_t v_stop_boxed_293_; lean_object* v_res_294_; 
v_i_boxed_292_ = lean_unbox_usize(v_i_289_);
lean_dec(v_i_289_);
v_stop_boxed_293_ = lean_unbox_usize(v_stop_290_);
lean_dec(v_stop_290_);
v_res_294_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_attachToPull_spec__0(v_as_288_, v_i_boxed_292_, v_stop_boxed_293_, v_b_291_);
lean_dec_ref(v_as_288_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_attachToPull___redArg(lean_object* v_c_295_, lean_object* v_a_296_){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_298_ = lean_st_ref_get(v_a_296_);
v___x_299_ = lean_array_get_size(v___x_298_);
v___x_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = lean_nat_dec_lt(v___x_300_, v___x_299_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; 
lean_dec(v___x_298_);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v_c_295_);
return v___x_302_;
}
else
{
size_t v___x_303_; size_t v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_303_ = lean_usize_of_nat(v___x_299_);
v___x_304_ = ((size_t)0ULL);
v___x_305_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_attachToPull_spec__0(v___x_298_, v___x_303_, v___x_304_, v_c_295_);
lean_dec(v___x_298_);
v___x_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_attachToPull___redArg___boxed(lean_object* v_c_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Compiler_LCNF_PullLetDecls_attachToPull___redArg(v_c_307_, v_a_308_);
lean_dec(v_a_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_attachToPull(lean_object* v_c_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_Compiler_LCNF_PullLetDecls_attachToPull___redArg(v_c_311_, v_a_313_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_attachToPull___boxed(lean_object* v_c_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Compiler_LCNF_PullLetDecls_attachToPull(v_c_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_shouldPull(lean_object* v_decl_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_isCandidateFn_341_; lean_object* v_included_342_; uint8_t v___x_343_; uint8_t v___x_344_; 
v_isCandidateFn_341_ = lean_ctor_get(v_a_330_, 0);
v_included_342_ = lean_ctor_get(v_a_330_, 1);
v___x_343_ = 0;
v___x_344_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v___x_343_, v_decl_329_, v_included_342_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; 
lean_inc_ref(v_isCandidateFn_341_);
lean_inc(v_a_335_);
lean_inc_ref(v_a_334_);
lean_inc(v_a_333_);
lean_inc_ref(v_a_332_);
lean_inc(v_included_342_);
lean_inc_ref(v_decl_329_);
v___x_345_ = lean_apply_7(v_isCandidateFn_341_, v_decl_329_, v_included_342_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, lean_box(0));
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_357_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_357_ == 0)
{
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_357_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_357_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
uint8_t v___x_350_; 
v___x_350_ = lean_unbox(v_a_346_);
if (v___x_350_ == 0)
{
lean_del_object(v___x_348_);
lean_dec(v_a_346_);
lean_dec_ref(v_decl_329_);
goto v___jp_337_;
}
else
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_351_ = lean_st_ref_take(v_a_331_);
v___x_352_ = lean_array_push(v___x_351_, v_decl_329_);
v___x_353_ = lean_st_ref_put(v_a_331_, v___x_352_);
if (v_isShared_349_ == 0)
{
v___x_355_ = v___x_348_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_346_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_dec_ref(v_decl_329_);
return v___x_345_;
}
}
else
{
lean_dec_ref(v_decl_329_);
goto v___jp_337_;
}
v___jp_337_:
{
uint8_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = 0;
v___x_339_ = lean_box(v___x_338_);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_shouldPull___boxed(lean_object* v_decl_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Compiler_LCNF_PullLetDecls_shouldPull(v_decl_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(lean_object* v_as_367_, size_t v_i_368_, size_t v_stop_369_, lean_object* v_b_370_){
_start:
{
uint8_t v___x_371_; 
v___x_371_ = lean_usize_dec_eq(v_i_368_, v_stop_369_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v_fvarId_373_; lean_object* v___x_374_; size_t v___x_375_; size_t v___x_376_; 
v___x_372_ = lean_array_uget_borrowed(v_as_367_, v_i_368_);
v_fvarId_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_fvarId_373_);
v___x_374_ = l_Lean_FVarIdSet_insert(v_b_370_, v_fvarId_373_);
v___x_375_ = ((size_t)1ULL);
v___x_376_ = lean_usize_add(v_i_368_, v___x_375_);
v_i_368_ = v___x_376_;
v_b_370_ = v___x_374_;
goto _start;
}
else
{
return v_b_370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0___boxed(lean_object* v_as_378_, lean_object* v_i_379_, lean_object* v_stop_380_, lean_object* v_b_381_){
_start:
{
size_t v_i_boxed_382_; size_t v_stop_boxed_383_; lean_object* v_res_384_; 
v_i_boxed_382_ = lean_unbox_usize(v_i_379_);
lean_dec(v_i_379_);
v_stop_boxed_383_ = lean_unbox_usize(v_stop_380_);
lean_dec(v_stop_380_);
v_res_384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_as_378_, v_i_boxed_382_, v_stop_boxed_383_, v_b_381_);
lean_dec_ref(v_as_378_);
return v_res_384_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2___closed__0(void){
_start:
{
uint8_t v___x_385_; lean_object* v___x_386_; 
v___x_385_ = 0;
v___x_386_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2(lean_object* v_msg_387_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2___closed__0, &l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2___closed__0);
v___x_389_ = lean_panic_fn_borrowed(v___x_388_, v_msg_387_);
return v___x_389_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__3(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_393_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__2));
v___x_394_ = lean_unsigned_to_nat(9u);
v___x_395_ = lean_unsigned_to_nat(641u);
v___x_396_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__1));
v___x_397_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__0));
v___x_398_ = l_mkPanicMessageWithDecl(v___x_397_, v___x_396_, v___x_395_, v___x_394_, v___x_393_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0(uint8_t v___x_399_, lean_object* v_decl_400_, lean_object* v_type_401_, lean_object* v_params_402_, lean_object* v_k_403_, lean_object* v_code_404_, lean_object* v_value_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_isCandidateFn_413_; lean_object* v_included_414_; lean_object* v___y_416_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v_isCandidateFn_413_ = lean_ctor_get(v___y_406_, 0);
v_included_414_ = lean_ctor_get(v___y_406_, 1);
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = lean_array_get_size(v_params_402_);
v___x_524_ = lean_nat_dec_lt(v___x_522_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; 
lean_inc(v_included_414_);
lean_inc_ref(v_isCandidateFn_413_);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v_isCandidateFn_413_);
lean_ctor_set(v___x_525_, 1, v_included_414_);
v___x_526_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_value_405_, v___x_525_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec_ref_known(v___x_525_, 2);
v___y_416_ = v___x_526_;
goto v___jp_415_;
}
else
{
size_t v___x_527_; size_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_527_ = ((size_t)0ULL);
v___x_528_ = lean_usize_of_nat(v___x_523_);
lean_inc(v_included_414_);
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_402_, v___x_527_, v___x_528_, v_included_414_);
lean_inc_ref(v_isCandidateFn_413_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v_isCandidateFn_413_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_value_405_, v___x_530_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec_ref_known(v___x_530_, 2);
v___y_416_ = v___x_531_;
goto v___jp_415_;
}
v___jp_415_:
{
if (lean_obj_tag(v___y_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_418_; 
v_a_417_ = lean_ctor_get(v___y_416_, 0);
lean_inc(v_a_417_);
lean_dec_ref_known(v___y_416_, 1);
v___x_418_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_399_, v_decl_400_, v_type_401_, v_params_402_, v_a_417_, v___y_409_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v_fvarId_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref_known(v___x_418_, 1);
v_fvarId_420_ = lean_ctor_get(v_a_419_, 0);
lean_inc(v_fvarId_420_);
lean_inc(v_included_414_);
v___x_421_ = l_Lean_FVarIdSet_insert(v_included_414_, v_fvarId_420_);
lean_inc_ref(v_isCandidateFn_413_);
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v_isCandidateFn_413_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_k_403_, v___x_422_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec_ref_known(v___x_422_, 2);
if (lean_obj_tag(v___x_423_) == 0)
{
switch(lean_obj_tag(v_code_404_))
{
case 1:
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_463_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_463_ == 0)
{
v___x_426_ = v___x_423_;
v_isShared_427_ = v_isSharedCheck_463_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_423_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_463_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v_decl_428_; lean_object* v_k_429_; size_t v___x_430_; size_t v___x_431_; uint8_t v___x_432_; 
v_decl_428_ = lean_ctor_get(v_code_404_, 0);
v_k_429_ = lean_ctor_get(v_code_404_, 1);
v___x_430_ = lean_ptr_addr(v_k_429_);
v___x_431_ = lean_ptr_addr(v_a_424_);
v___x_432_ = lean_usize_dec_eq(v___x_430_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_442_; 
v_isSharedCheck_442_ = !lean_is_exclusive(v_code_404_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; lean_object* v_unused_444_; 
v_unused_443_ = lean_ctor_get(v_code_404_, 1);
lean_dec(v_unused_443_);
v_unused_444_ = lean_ctor_get(v_code_404_, 0);
lean_dec(v_unused_444_);
v___x_434_ = v_code_404_;
v_isShared_435_ = v_isSharedCheck_442_;
goto v_resetjp_433_;
}
else
{
lean_dec(v_code_404_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_442_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v_a_424_);
lean_ctor_set(v___x_434_, 0, v_a_419_);
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_419_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_a_424_);
v___x_437_ = v_reuseFailAlloc_441_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_439_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_437_);
v___x_439_ = v___x_426_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
else
{
size_t v___x_445_; size_t v___x_446_; uint8_t v___x_447_; 
v___x_445_ = lean_ptr_addr(v_decl_428_);
v___x_446_ = lean_ptr_addr(v_a_419_);
v___x_447_ = lean_usize_dec_eq(v___x_445_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_457_; 
v_isSharedCheck_457_ = !lean_is_exclusive(v_code_404_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; lean_object* v_unused_459_; 
v_unused_458_ = lean_ctor_get(v_code_404_, 1);
lean_dec(v_unused_458_);
v_unused_459_ = lean_ctor_get(v_code_404_, 0);
lean_dec(v_unused_459_);
v___x_449_ = v_code_404_;
v_isShared_450_ = v_isSharedCheck_457_;
goto v_resetjp_448_;
}
else
{
lean_dec(v_code_404_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_457_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v_a_424_);
lean_ctor_set(v___x_449_, 0, v_a_419_);
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_419_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_a_424_);
v___x_452_ = v_reuseFailAlloc_456_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_454_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_452_);
v___x_454_ = v___x_426_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
else
{
lean_object* v___x_461_; 
lean_dec(v_a_424_);
lean_dec(v_a_419_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v_code_404_);
v___x_461_ = v___x_426_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_code_404_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
case 2:
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_503_; 
v_a_464_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_503_ == 0)
{
v___x_466_ = v___x_423_;
v_isShared_467_ = v_isSharedCheck_503_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_423_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_503_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v_decl_468_; lean_object* v_k_469_; size_t v___x_470_; size_t v___x_471_; uint8_t v___x_472_; 
v_decl_468_ = lean_ctor_get(v_code_404_, 0);
v_k_469_ = lean_ctor_get(v_code_404_, 1);
v___x_470_ = lean_ptr_addr(v_k_469_);
v___x_471_ = lean_ptr_addr(v_a_464_);
v___x_472_ = lean_usize_dec_eq(v___x_470_, v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_482_; 
v_isSharedCheck_482_ = !lean_is_exclusive(v_code_404_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; lean_object* v_unused_484_; 
v_unused_483_ = lean_ctor_get(v_code_404_, 1);
lean_dec(v_unused_483_);
v_unused_484_ = lean_ctor_get(v_code_404_, 0);
lean_dec(v_unused_484_);
v___x_474_ = v_code_404_;
v_isShared_475_ = v_isSharedCheck_482_;
goto v_resetjp_473_;
}
else
{
lean_dec(v_code_404_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_482_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 1, v_a_464_);
lean_ctor_set(v___x_474_, 0, v_a_419_);
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_419_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_a_464_);
v___x_477_ = v_reuseFailAlloc_481_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_479_; 
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_477_);
v___x_479_ = v___x_466_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
else
{
size_t v___x_485_; size_t v___x_486_; uint8_t v___x_487_; 
v___x_485_ = lean_ptr_addr(v_decl_468_);
v___x_486_ = lean_ptr_addr(v_a_419_);
v___x_487_ = lean_usize_dec_eq(v___x_485_, v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_497_; 
v_isSharedCheck_497_ = !lean_is_exclusive(v_code_404_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; lean_object* v_unused_499_; 
v_unused_498_ = lean_ctor_get(v_code_404_, 1);
lean_dec(v_unused_498_);
v_unused_499_ = lean_ctor_get(v_code_404_, 0);
lean_dec(v_unused_499_);
v___x_489_ = v_code_404_;
v_isShared_490_ = v_isSharedCheck_497_;
goto v_resetjp_488_;
}
else
{
lean_dec(v_code_404_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_497_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v_a_464_);
lean_ctor_set(v___x_489_, 0, v_a_419_);
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_419_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_a_464_);
v___x_492_ = v_reuseFailAlloc_496_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_494_; 
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_492_);
v___x_494_ = v___x_466_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
else
{
lean_object* v___x_501_; 
lean_dec(v_a_464_);
lean_dec(v_a_419_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v_code_404_);
v___x_501_ = v___x_466_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_code_404_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
default: 
{
lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_512_; 
lean_dec(v_a_419_);
lean_dec_ref(v_code_404_);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; 
v_unused_513_ = lean_ctor_get(v___x_423_, 0);
lean_dec(v_unused_513_);
v___x_505_ = v___x_423_;
v_isShared_506_ = v_isSharedCheck_512_;
goto v_resetjp_504_;
}
else
{
lean_dec(v___x_423_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_512_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_507_ = lean_obj_once(&l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__3, &l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__3_once, _init_l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__3);
v___x_508_ = l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2(v___x_507_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_508_);
v___x_510_ = v___x_505_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
else
{
lean_dec(v_a_419_);
lean_dec_ref(v_code_404_);
return v___x_423_;
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_dec_ref(v_code_404_);
lean_dec_ref(v_k_403_);
v_a_514_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_418_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_418_);
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
else
{
lean_dec_ref(v_code_404_);
lean_dec_ref(v_k_403_);
lean_dec_ref(v_params_402_);
lean_dec_ref(v_type_401_);
lean_dec_ref(v_decl_400_);
return v___y_416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___boxed(lean_object* v___x_532_, lean_object* v_decl_533_, lean_object* v_type_534_, lean_object* v_params_535_, lean_object* v_k_536_, lean_object* v_code_537_, lean_object* v_value_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
uint8_t v___x_4285__boxed_546_; lean_object* v_res_547_; 
v___x_4285__boxed_546_ = lean_unbox(v___x_532_);
v_res_547_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0(v___x_4285__boxed_546_, v_decl_533_, v_type_534_, v_params_535_, v_k_536_, v_code_537_, v_value_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__1___boxed(lean_object* v___x_548_, lean_object* v_alts_549_, lean_object* v_typeName_550_, lean_object* v_resultType_551_, lean_object* v_discr_552_, lean_object* v_code_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__1(v___x_548_, v_alts_549_, v_typeName_550_, v_resultType_551_, v_discr_552_, v_code_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(lean_object* v_code_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_decl_571_; lean_object* v_k_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; 
switch(lean_obj_tag(v_code_562_))
{
case 4:
{
lean_object* v_cases_586_; lean_object* v_typeName_587_; lean_object* v_resultType_588_; lean_object* v_discr_589_; lean_object* v_alts_590_; lean_object* v___x_591_; lean_object* v___f_592_; lean_object* v___x_593_; 
v_cases_586_ = lean_ctor_get(v_code_562_, 0);
v_typeName_587_ = lean_ctor_get(v_cases_586_, 0);
lean_inc(v_typeName_587_);
v_resultType_588_ = lean_ctor_get(v_cases_586_, 1);
lean_inc_ref(v_resultType_588_);
v_discr_589_ = lean_ctor_get(v_cases_586_, 2);
lean_inc(v_discr_589_);
v_alts_590_ = lean_ctor_get(v_cases_586_, 3);
lean_inc_ref(v_alts_590_);
v___x_591_ = lean_unsigned_to_nat(0u);
v___f_592_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__1___boxed), 13, 6);
lean_closure_set(v___f_592_, 0, v___x_591_);
lean_closure_set(v___f_592_, 1, v_alts_590_);
lean_closure_set(v___f_592_, 2, v_typeName_587_);
lean_closure_set(v___f_592_, 3, v_resultType_588_);
lean_closure_set(v___f_592_, 4, v_discr_589_);
lean_closure_set(v___f_592_, 5, v_code_562_);
v___x_593_ = l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint(v___f_592_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
return v___x_593_;
}
case 0:
{
lean_object* v_decl_594_; lean_object* v_k_595_; lean_object* v___x_596_; 
v_decl_594_ = lean_ctor_get(v_code_562_, 0);
v_k_595_ = lean_ctor_get(v_code_562_, 1);
lean_inc_ref(v_decl_594_);
v___x_596_ = l_Lean_Compiler_LCNF_PullLetDecls_shouldPull(v_decl_594_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; uint8_t v___x_598_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_596_, 1);
v___x_598_ = lean_unbox(v_a_597_);
lean_dec(v_a_597_);
if (v___x_598_ == 0)
{
lean_object* v_fvarId_599_; lean_object* v_isCandidateFn_600_; lean_object* v_included_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v_fvarId_599_ = lean_ctor_get(v_decl_594_, 0);
v_isCandidateFn_600_ = lean_ctor_get(v_a_563_, 0);
v_included_601_ = lean_ctor_get(v_a_563_, 1);
lean_inc(v_fvarId_599_);
lean_inc(v_included_601_);
v___x_602_ = l_Lean_FVarIdSet_insert(v_included_601_, v_fvarId_599_);
lean_inc_ref(v_isCandidateFn_600_);
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v_isCandidateFn_600_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
lean_inc_ref(v_k_595_);
v___x_604_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_k_595_, v___x_603_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec_ref_known(v___x_603_, 2);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_627_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_627_ == 0)
{
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_627_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_627_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
size_t v___x_609_; size_t v___x_610_; uint8_t v___x_611_; 
v___x_609_ = lean_ptr_addr(v_k_595_);
v___x_610_ = lean_ptr_addr(v_a_605_);
v___x_611_ = lean_usize_dec_eq(v___x_609_, v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_621_; 
lean_inc_ref(v_decl_594_);
v_isSharedCheck_621_ = !lean_is_exclusive(v_code_562_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; lean_object* v_unused_623_; 
v_unused_622_ = lean_ctor_get(v_code_562_, 1);
lean_dec(v_unused_622_);
v_unused_623_ = lean_ctor_get(v_code_562_, 0);
lean_dec(v_unused_623_);
v___x_613_ = v_code_562_;
v_isShared_614_ = v_isSharedCheck_621_;
goto v_resetjp_612_;
}
else
{
lean_dec(v_code_562_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_621_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v_a_605_);
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_decl_594_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_a_605_);
v___x_616_ = v_reuseFailAlloc_620_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_618_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_616_);
v___x_618_ = v___x_607_;
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
}
else
{
lean_object* v___x_625_; 
lean_dec(v_a_605_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v_code_562_);
v___x_625_ = v___x_607_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_code_562_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_562_, 2);
return v___x_604_;
}
}
else
{
lean_inc_ref(v_k_595_);
lean_dec_ref_known(v_code_562_, 2);
v_code_562_ = v_k_595_;
goto _start;
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec_ref_known(v_code_562_, 2);
v_a_629_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_596_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_596_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
case 1:
{
lean_object* v_decl_637_; lean_object* v_k_638_; 
v_decl_637_ = lean_ctor_get(v_code_562_, 0);
v_k_638_ = lean_ctor_get(v_code_562_, 1);
lean_inc_ref(v_k_638_);
lean_inc_ref(v_decl_637_);
v_decl_571_ = v_decl_637_;
v_k_572_ = v_k_638_;
v___y_573_ = v_a_563_;
v___y_574_ = v_a_564_;
v___y_575_ = v_a_565_;
v___y_576_ = v_a_566_;
v___y_577_ = v_a_567_;
v___y_578_ = v_a_568_;
goto v___jp_570_;
}
case 2:
{
lean_object* v_decl_639_; lean_object* v_k_640_; 
v_decl_639_ = lean_ctor_get(v_code_562_, 0);
v_k_640_ = lean_ctor_get(v_code_562_, 1);
lean_inc_ref(v_k_640_);
lean_inc_ref(v_decl_639_);
v_decl_571_ = v_decl_639_;
v_k_572_ = v_k_640_;
v___y_573_ = v_a_563_;
v___y_574_ = v_a_564_;
v___y_575_ = v_a_565_;
v___y_576_ = v_a_566_;
v___y_577_ = v_a_567_;
v___y_578_ = v_a_568_;
goto v___jp_570_;
}
default: 
{
lean_object* v___x_641_; 
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v_code_562_);
return v___x_641_;
}
}
v___jp_570_:
{
lean_object* v_params_579_; lean_object* v_type_580_; lean_object* v_value_581_; uint8_t v___x_582_; lean_object* v___x_583_; lean_object* v___f_584_; lean_object* v___x_585_; 
v_params_579_ = lean_ctor_get(v_decl_571_, 2);
lean_inc_ref(v_params_579_);
v_type_580_ = lean_ctor_get(v_decl_571_, 3);
lean_inc_ref(v_type_580_);
v_value_581_ = lean_ctor_get(v_decl_571_, 4);
lean_inc_ref(v_value_581_);
v___x_582_ = 0;
v___x_583_ = lean_box(v___x_582_);
v___f_584_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___boxed), 14, 7);
lean_closure_set(v___f_584_, 0, v___x_583_);
lean_closure_set(v___f_584_, 1, v_decl_571_);
lean_closure_set(v___f_584_, 2, v_type_580_);
lean_closure_set(v___f_584_, 3, v_params_579_);
lean_closure_set(v___f_584_, 4, v_k_572_);
lean_closure_set(v___f_584_, 5, v_code_562_);
lean_closure_set(v___f_584_, 6, v_value_581_);
v___x_585_ = l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint(v___f_584_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullAlt(lean_object* v_alt_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
lean_object* v___y_651_; 
if (lean_obj_tag(v_alt_642_) == 0)
{
lean_object* v_params_669_; lean_object* v_code_670_; lean_object* v_isCandidateFn_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v_params_669_ = lean_ctor_get(v_alt_642_, 1);
v_code_670_ = lean_ctor_get(v_alt_642_, 2);
v_isCandidateFn_671_ = lean_ctor_get(v_a_643_, 0);
v___x_672_ = lean_box(1);
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = lean_array_get_size(v_params_669_);
v___x_675_ = lean_nat_dec_lt(v___x_673_, v___x_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; 
lean_inc_ref(v_isCandidateFn_671_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_isCandidateFn_671_);
lean_ctor_set(v___x_676_, 1, v___x_672_);
lean_inc_ref(v_code_670_);
v___x_677_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_code_670_, v___x_676_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_);
lean_dec_ref_known(v___x_676_, 2);
v___y_651_ = v___x_677_;
goto v___jp_650_;
}
else
{
size_t v___x_678_; size_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_678_ = ((size_t)0ULL);
v___x_679_ = lean_usize_of_nat(v___x_674_);
v___x_680_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_669_, v___x_678_, v___x_679_, v___x_672_);
lean_inc_ref(v_isCandidateFn_671_);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v_isCandidateFn_671_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
lean_inc_ref(v_code_670_);
v___x_682_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_code_670_, v___x_681_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_);
lean_dec_ref_known(v___x_681_, 2);
v___y_651_ = v___x_682_;
goto v___jp_650_;
}
}
else
{
lean_object* v_code_683_; lean_object* v_isCandidateFn_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_code_683_ = lean_ctor_get(v_alt_642_, 0);
v_isCandidateFn_684_ = lean_ctor_get(v_a_643_, 0);
v___x_685_ = lean_box(1);
lean_inc_ref(v_isCandidateFn_684_);
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v_isCandidateFn_684_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
lean_inc_ref(v_code_683_);
v___x_687_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_code_683_, v___x_686_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_);
lean_dec_ref_known(v___x_686_, 2);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_696_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_696_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_696_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_696_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_692_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_642_, v_a_688_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_692_);
v___x_694_ = v___x_690_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec_ref_known(v_alt_642_, 1);
v_a_697_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_687_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_687_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
v___jp_650_:
{
if (lean_obj_tag(v___y_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_660_; 
v_a_652_ = lean_ctor_get(v___y_651_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___y_651_);
if (v_isSharedCheck_660_ == 0)
{
v___x_654_ = v___y_651_;
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___y_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_656_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_642_, v_a_652_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_656_);
v___x_658_ = v___x_654_;
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
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec_ref(v_alt_642_);
v_a_661_ = lean_ctor_get(v___y_651_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___y_651_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___y_651_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___y_651_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__3(lean_object* v_i_705_, lean_object* v_as_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = lean_array_get_size(v_as_706_);
v___x_715_ = lean_nat_dec_lt(v_i_705_, v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
lean_dec(v_i_705_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v_as_706_);
return v___x_716_;
}
else
{
lean_object* v_a_717_; lean_object* v___x_718_; 
v_a_717_ = lean_array_fget_borrowed(v_as_706_, v_i_705_);
lean_inc(v_a_717_);
v___x_718_ = l_Lean_Compiler_LCNF_PullLetDecls_pullAlt(v_a_717_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; size_t v___x_720_; size_t v___x_721_; uint8_t v___x_722_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
v___x_720_ = lean_ptr_addr(v_a_717_);
v___x_721_ = lean_ptr_addr(v_a_719_);
v___x_722_ = lean_usize_dec_eq(v___x_720_, v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_723_ = lean_unsigned_to_nat(1u);
v___x_724_ = lean_nat_add(v_i_705_, v___x_723_);
v___x_725_ = lean_array_fset(v_as_706_, v_i_705_, v_a_719_);
lean_dec(v_i_705_);
v_i_705_ = v___x_724_;
v_as_706_ = v___x_725_;
goto _start;
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; 
lean_dec(v_a_719_);
v___x_727_ = lean_unsigned_to_nat(1u);
v___x_728_ = lean_nat_add(v_i_705_, v___x_727_);
lean_dec(v_i_705_);
v_i_705_ = v___x_728_;
goto _start;
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v_as_706_);
lean_dec(v_i_705_);
v_a_730_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_718_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_718_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__1(lean_object* v___x_738_, lean_object* v_alts_739_, lean_object* v_typeName_740_, lean_object* v_resultType_741_, lean_object* v_discr_742_, lean_object* v_code_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v___x_751_; 
lean_inc_ref(v_alts_739_);
v___x_751_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__3(v___x_738_, v_alts_739_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_767_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_767_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_767_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_767_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
size_t v___x_756_; size_t v___x_757_; uint8_t v___x_758_; 
v___x_756_ = lean_ptr_addr(v_alts_739_);
lean_dec_ref(v_alts_739_);
v___x_757_ = lean_ptr_addr(v_a_752_);
v___x_758_ = lean_usize_dec_eq(v___x_756_, v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
lean_dec_ref(v_code_743_);
v___x_759_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_759_, 0, v_typeName_740_);
lean_ctor_set(v___x_759_, 1, v_resultType_741_);
lean_ctor_set(v___x_759_, 2, v_discr_742_);
lean_ctor_set(v___x_759_, 3, v_a_752_);
v___x_760_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_760_);
v___x_762_ = v___x_754_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
else
{
lean_object* v___x_765_; 
lean_dec(v_a_752_);
lean_dec(v_discr_742_);
lean_dec_ref(v_resultType_741_);
lean_dec(v_typeName_740_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v_code_743_);
v___x_765_ = v___x_754_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_code_743_);
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
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec_ref(v_code_743_);
lean_dec(v_discr_742_);
lean_dec_ref(v_resultType_741_);
lean_dec(v_typeName_740_);
lean_dec_ref(v_alts_739_);
v_a_768_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_751_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_751_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__3___boxed(lean_object* v_i_776_, lean_object* v_as_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__3(v_i_776_, v_as_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullAlt___boxed(lean_object* v_alt_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_Compiler_LCNF_PullLetDecls_pullAlt(v_alt_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___boxed(lean_object* v_code_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_code_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg(lean_object* v_x_804_, lean_object* v_isCandidateFn_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_811_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint___closed__0));
v___x_812_ = lean_st_mk_ref(v___x_811_);
v___x_813_ = lean_box(1);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v_isCandidateFn_805_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
lean_inc(v_a_809_);
lean_inc_ref(v_a_808_);
lean_inc(v_a_807_);
lean_inc_ref(v_a_806_);
lean_inc(v___x_812_);
v___x_815_ = lean_apply_7(v_x_804_, v___x_814_, v___x_812_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, lean_box(0));
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_824_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_824_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_820_ = lean_st_ref_get(v___x_812_);
lean_dec(v___x_812_);
lean_dec(v___x_820_);
if (v_isShared_819_ == 0)
{
v___x_822_ = v___x_818_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_816_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
else
{
lean_dec(v___x_812_);
return v___x_815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg___boxed(lean_object* v_x_825_, lean_object* v_isCandidateFn_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg(v_x_825_, v_isCandidateFn_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_PullM_run(lean_object* v_00_u03b1_833_, lean_object* v_x_834_, lean_object* v_isCandidateFn_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg(v_x_834_, v_isCandidateFn_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___boxed(lean_object* v_00_u03b1_842_, lean_object* v_x_843_, lean_object* v_isCandidateFn_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_Compiler_LCNF_PullLetDecls_PullM_run(v_00_u03b1_842_, v_x_843_, v_isCandidateFn_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(lean_object* v_f_851_, lean_object* v_v_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
if (lean_obj_tag(v_v_852_) == 0)
{
lean_object* v_code_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_884_; 
v_code_860_ = lean_ctor_get(v_v_852_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v_v_852_);
if (v_isSharedCheck_884_ == 0)
{
v___x_862_ = v_v_852_;
v_isShared_863_ = v_isSharedCheck_884_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_code_860_);
lean_dec(v_v_852_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_884_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; 
lean_inc(v___y_858_);
lean_inc_ref(v___y_857_);
lean_inc(v___y_856_);
lean_inc_ref(v___y_855_);
lean_inc(v___y_854_);
lean_inc_ref(v___y_853_);
v___x_864_ = lean_apply_8(v_f_851_, v_code_860_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, lean_box(0));
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_875_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_875_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_875_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_875_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v_a_865_);
v___x_870_ = v___x_862_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_874_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_872_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_870_);
v___x_872_ = v___x_867_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_del_object(v___x_862_);
v_a_876_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_864_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_864_);
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
else
{
lean_object* v___x_885_; 
lean_dec_ref(v_f_851_);
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v_v_852_);
return v___x_885_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg___boxed(lean_object* v_f_886_, lean_object* v_v_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(v_f_886_, v_v_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0(uint8_t v_pu_896_, lean_object* v_f_897_, lean_object* v_v_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(v_f_897_, v_v_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___boxed(lean_object* v_pu_907_, lean_object* v_f_908_, lean_object* v_v_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
uint8_t v_pu_boxed_917_; lean_object* v_res_918_; 
v_pu_boxed_917_ = lean_unbox(v_pu_907_);
v_res_918_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0(v_pu_boxed_917_, v_f_908_, v_v_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0(lean_object* v___x_920_, lean_object* v_value_921_, lean_object* v_toSignature_922_, uint8_t v_recursive_923_, lean_object* v_inlineAttr_x3f_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(v___x_920_, v_value_921_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_932_, 1);
v___x_934_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0___closed__0));
v___x_935_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(v___x_934_, v_a_933_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_944_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_944_ == 0)
{
v___x_938_ = v___x_935_;
v_isShared_939_ = v_isSharedCheck_944_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_944_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_940_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_940_, 0, v_toSignature_922_);
lean_ctor_set(v___x_940_, 1, v_a_936_);
lean_ctor_set(v___x_940_, 2, v_inlineAttr_x3f_924_);
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*3, v_recursive_923_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_940_);
v___x_942_ = v___x_938_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_940_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec(v_inlineAttr_x3f_924_);
lean_dec_ref(v_toSignature_922_);
v_a_945_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_935_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_935_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec(v_inlineAttr_x3f_924_);
lean_dec_ref(v_toSignature_922_);
v_a_953_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_932_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_932_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0___boxed(lean_object* v___x_961_, lean_object* v_value_962_, lean_object* v_toSignature_963_, lean_object* v_recursive_964_, lean_object* v_inlineAttr_x3f_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
uint8_t v_recursive_boxed_973_; lean_object* v_res_974_; 
v_recursive_boxed_973_ = lean_unbox(v_recursive_964_);
v_res_974_ = l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0(v___x_961_, v_value_962_, v_toSignature_963_, v_recursive_boxed_973_, v_inlineAttr_x3f_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__1(lean_object* v_params_975_, lean_object* v___f_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_isCandidateFn_984_; lean_object* v_included_985_; lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v_isCandidateFn_984_ = lean_ctor_get(v___y_977_, 0);
v_included_985_ = lean_ctor_get(v___y_977_, 1);
v___x_986_ = lean_unsigned_to_nat(0u);
v___x_987_ = lean_array_get_size(v_params_975_);
v___x_988_ = lean_nat_dec_lt(v___x_986_, v___x_987_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; 
v___x_989_ = lean_apply_7(v___f_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, lean_box(0));
return v___x_989_;
}
else
{
lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1000_; 
lean_inc(v_included_985_);
lean_inc_ref(v_isCandidateFn_984_);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___y_977_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; lean_object* v_unused_1002_; 
v_unused_1001_ = lean_ctor_get(v___y_977_, 1);
lean_dec(v_unused_1001_);
v_unused_1002_ = lean_ctor_get(v___y_977_, 0);
lean_dec(v_unused_1002_);
v___x_991_ = v___y_977_;
v_isShared_992_ = v_isSharedCheck_1000_;
goto v_resetjp_990_;
}
else
{
lean_dec(v___y_977_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1000_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
size_t v___x_993_; size_t v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_993_ = ((size_t)0ULL);
v___x_994_ = lean_usize_of_nat(v___x_987_);
v___x_995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_975_, v___x_993_, v___x_994_, v_included_985_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 1, v___x_995_);
v___x_997_ = v___x_991_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_isCandidateFn_984_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v___x_995_);
v___x_997_ = v_reuseFailAlloc_999_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; 
v___x_998_ = lean_apply_7(v___f_976_, v___x_997_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, lean_box(0));
return v___x_998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__1___boxed(lean_object* v_params_1003_, lean_object* v___f_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__1(v_params_1003_, v___f_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec_ref(v_params_1003_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls(lean_object* v_decl_1014_, lean_object* v_isCandidateFn_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v_toSignature_1021_; lean_object* v_value_1022_; uint8_t v_recursive_1023_; lean_object* v_inlineAttr_x3f_1024_; lean_object* v_params_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___f_1028_; lean_object* v___f_1029_; lean_object* v___x_1030_; 
v_toSignature_1021_ = lean_ctor_get(v_decl_1014_, 0);
lean_inc_ref(v_toSignature_1021_);
v_value_1022_ = lean_ctor_get(v_decl_1014_, 1);
lean_inc_ref(v_value_1022_);
v_recursive_1023_ = lean_ctor_get_uint8(v_decl_1014_, sizeof(void*)*3);
v_inlineAttr_x3f_1024_ = lean_ctor_get(v_decl_1014_, 2);
lean_inc(v_inlineAttr_x3f_1024_);
lean_dec_ref(v_decl_1014_);
v_params_1025_ = lean_ctor_get(v_toSignature_1021_, 3);
lean_inc_ref(v_params_1025_);
v___x_1026_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_pullLetDecls___closed__0));
v___x_1027_ = lean_box(v_recursive_1023_);
v___f_1028_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1028_, 0, v___x_1026_);
lean_closure_set(v___f_1028_, 1, v_value_1022_);
lean_closure_set(v___f_1028_, 2, v_toSignature_1021_);
lean_closure_set(v___f_1028_, 3, v___x_1027_);
lean_closure_set(v___f_1028_, 4, v_inlineAttr_x3f_1024_);
v___f_1029_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__1___boxed), 9, 2);
lean_closure_set(v___f_1029_, 0, v_params_1025_);
lean_closure_set(v___f_1029_, 1, v___f_1028_);
v___x_1030_ = l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg(v___f_1029_, v_isCandidateFn_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___boxed(lean_object* v_decl_1031_, lean_object* v_isCandidateFn_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_Compiler_LCNF_Decl_pullLetDecls(v_decl_1031_, v_isCandidateFn_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
return v_res_1038_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg(lean_object* v_k_1039_, lean_object* v_t_1040_){
_start:
{
if (lean_obj_tag(v_t_1040_) == 0)
{
lean_object* v_k_1041_; lean_object* v_l_1042_; lean_object* v_r_1043_; uint8_t v___x_1044_; 
v_k_1041_ = lean_ctor_get(v_t_1040_, 1);
v_l_1042_ = lean_ctor_get(v_t_1040_, 3);
v_r_1043_ = lean_ctor_get(v_t_1040_, 4);
v___x_1044_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1039_, v_k_1041_);
switch(v___x_1044_)
{
case 0:
{
v_t_1040_ = v_l_1042_;
goto _start;
}
case 1:
{
uint8_t v___x_1046_; 
v___x_1046_ = 1;
return v___x_1046_;
}
default: 
{
v_t_1040_ = v_r_1043_;
goto _start;
}
}
}
else
{
uint8_t v___x_1048_; 
v___x_1048_ = 0;
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg___boxed(lean_object* v_k_1049_, lean_object* v_t_1050_){
_start:
{
uint8_t v_res_1051_; lean_object* v_r_1052_; 
v_res_1051_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg(v_k_1049_, v_t_1050_);
lean_dec(v_t_1050_);
lean_dec(v_k_1049_);
v_r_1052_ = lean_box(v_res_1051_);
return v_r_1052_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1(lean_object* v_as_1053_, size_t v_i_1054_, size_t v_stop_1055_){
_start:
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_usize_dec_eq(v_i_1054_, v_stop_1055_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1057_ = lean_array_uget_borrowed(v_as_1053_, v_i_1054_);
v___x_1058_ = lean_box(0);
v___x_1059_ = l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(v___x_1057_, v___x_1058_);
if (v___x_1059_ == 0)
{
size_t v___x_1060_; size_t v___x_1061_; 
v___x_1060_ = ((size_t)1ULL);
v___x_1061_ = lean_usize_add(v_i_1054_, v___x_1060_);
v_i_1054_ = v___x_1061_;
goto _start;
}
else
{
return v___x_1059_;
}
}
else
{
uint8_t v___x_1063_; 
v___x_1063_ = 0;
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1___boxed(lean_object* v_as_1064_, lean_object* v_i_1065_, lean_object* v_stop_1066_){
_start:
{
size_t v_i_boxed_1067_; size_t v_stop_boxed_1068_; uint8_t v_res_1069_; lean_object* v_r_1070_; 
v_i_boxed_1067_ = lean_unbox_usize(v_i_1065_);
lean_dec(v_i_1065_);
v_stop_boxed_1068_ = lean_unbox_usize(v_stop_1066_);
lean_dec(v_stop_1066_);
v_res_1069_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1(v_as_1064_, v_i_boxed_1067_, v_stop_boxed_1068_);
lean_dec_ref(v_as_1064_);
v_r_1070_ = lean_box(v_res_1069_);
return v_r_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullInstances___lam__0(lean_object* v_letDecl_1071_, lean_object* v_candidates_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v_type_1078_; lean_object* v_value_1079_; lean_object* v___y_1081_; lean_object* v___y_1113_; 
v_type_1078_ = lean_ctor_get(v_letDecl_1071_, 2);
v_value_1079_ = lean_ctor_get(v_letDecl_1071_, 3);
if (lean_obj_tag(v_value_1079_) == 3)
{
lean_object* v_args_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v_args_1124_ = lean_ctor_get(v_value_1079_, 2);
v___x_1125_ = lean_unsigned_to_nat(0u);
v___x_1126_ = lean_array_get_size(v_args_1124_);
v___x_1127_ = lean_nat_dec_lt(v___x_1125_, v___x_1126_);
if (v___x_1127_ == 0)
{
v___y_1113_ = v___y_1076_;
goto v___jp_1112_;
}
else
{
if (v___x_1127_ == 0)
{
v___y_1113_ = v___y_1076_;
goto v___jp_1112_;
}
else
{
size_t v___x_1128_; size_t v___x_1129_; uint8_t v___x_1130_; 
v___x_1128_ = ((size_t)0ULL);
v___x_1129_ = lean_usize_of_nat(v___x_1126_);
v___x_1130_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1(v_args_1124_, v___x_1128_, v___x_1129_);
if (v___x_1130_ == 0)
{
v___y_1113_ = v___y_1076_;
goto v___jp_1112_;
}
else
{
uint8_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1131_ = 0;
v___x_1132_ = lean_box(v___x_1131_);
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
return v___x_1133_;
}
}
}
}
else
{
v___y_1113_ = v___y_1076_;
goto v___jp_1112_;
}
v___jp_1080_:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_1078_, v___y_1081_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1103_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1103_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1103_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
if (lean_obj_tag(v_a_1083_) == 0)
{
if (lean_obj_tag(v_value_1079_) == 2)
{
lean_object* v_struct_1087_; uint8_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v_struct_1087_ = lean_ctor_get(v_value_1079_, 2);
v___x_1088_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg(v_struct_1087_, v_candidates_1072_);
v___x_1089_ = lean_box(v___x_1088_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1089_);
v___x_1091_ = v___x_1085_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
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
uint8_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1093_ = 0;
v___x_1094_ = lean_box(v___x_1093_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1094_);
v___x_1096_ = v___x_1085_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
else
{
uint8_t v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
lean_dec_ref_known(v_a_1083_, 1);
v___x_1098_ = 1;
v___x_1099_ = lean_box(v___x_1098_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1099_);
v___x_1101_ = v___x_1085_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
v_a_1104_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1082_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1082_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
v___jp_1112_:
{
if (lean_obj_tag(v_value_1079_) == 4)
{
lean_object* v_args_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_args_1114_ = lean_ctor_get(v_value_1079_, 1);
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1116_ = lean_array_get_size(v_args_1114_);
v___x_1117_ = lean_nat_dec_lt(v___x_1115_, v___x_1116_);
if (v___x_1117_ == 0)
{
v___y_1081_ = v___y_1113_;
goto v___jp_1080_;
}
else
{
if (v___x_1117_ == 0)
{
v___y_1081_ = v___y_1113_;
goto v___jp_1080_;
}
else
{
size_t v___x_1118_; size_t v___x_1119_; uint8_t v___x_1120_; 
v___x_1118_ = ((size_t)0ULL);
v___x_1119_ = lean_usize_of_nat(v___x_1116_);
v___x_1120_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1(v_args_1114_, v___x_1118_, v___x_1119_);
if (v___x_1120_ == 0)
{
v___y_1081_ = v___y_1113_;
goto v___jp_1080_;
}
else
{
uint8_t v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1121_ = 0;
v___x_1122_ = lean_box(v___x_1121_);
v___x_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
return v___x_1123_;
}
}
}
}
else
{
v___y_1081_ = v___y_1113_;
goto v___jp_1080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullInstances___lam__0___boxed(lean_object* v_letDecl_1134_, lean_object* v_candidates_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Compiler_LCNF_Decl_pullInstances___lam__0(v_letDecl_1134_, v_candidates_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v_candidates_1135_);
lean_dec_ref(v_letDecl_1134_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullInstances(lean_object* v_decl_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v___f_1149_; lean_object* v___x_1150_; 
v___f_1149_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_pullInstances___closed__0));
v___x_1150_ = l_Lean_Compiler_LCNF_Decl_pullLetDecls(v_decl_1143_, v___f_1149_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullInstances___boxed(lean_object* v_decl_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_Compiler_LCNF_Decl_pullInstances(v_decl_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
return v_res_1157_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0(lean_object* v_00_u03b2_1158_, lean_object* v_k_1159_, lean_object* v_t_1160_){
_start:
{
uint8_t v___x_1161_; 
v___x_1161_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg(v_k_1159_, v_t_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___boxed(lean_object* v_00_u03b2_1162_, lean_object* v_k_1163_, lean_object* v_t_1164_){
_start:
{
uint8_t v_res_1165_; lean_object* v_r_1166_; 
v_res_1165_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0(v_00_u03b2_1162_, v_k_1163_, v_t_1164_);
lean_dec(v_t_1164_);
lean_dec(v_k_1163_);
v_r_1166_ = lean_box(v_res_1165_);
return v_r_1166_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullInstances___closed__3(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1171_ = lean_unsigned_to_nat(0u);
v___x_1172_ = ((lean_object*)(l_Lean_Compiler_LCNF_pullInstances___closed__2));
v___x_1173_ = 0;
v___x_1174_ = ((lean_object*)(l_Lean_Compiler_LCNF_pullInstances___closed__1));
v___x_1175_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1174_, v___x_1173_, v___x_1172_, v___x_1171_);
return v___x_1175_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullInstances(void){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = lean_obj_once(&l_Lean_Compiler_LCNF_pullInstances___closed__3, &l_Lean_Compiler_LCNF_pullInstances___closed__3_once, _init_l_Lean_Compiler_LCNF_pullInstances___closed__3);
return v___x_1176_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1232_ = lean_unsigned_to_nat(3825914912u);
v___x_1233_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_));
v___x_1234_ = l_Lean_Name_num___override(v___x_1233_, v___x_1232_);
return v___x_1234_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1236_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_));
v___x_1237_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_);
v___x_1238_ = l_Lean_Name_str___override(v___x_1237_, v___x_1236_);
return v___x_1238_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_));
v___x_1241_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_);
v___x_1242_ = l_Lean_Name_str___override(v___x_1241_, v___x_1240_);
return v___x_1242_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1243_ = lean_unsigned_to_nat(2u);
v___x_1244_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_);
v___x_1245_ = l_Lean_Name_num___override(v___x_1244_, v___x_1243_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1247_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_));
v___x_1248_ = 1;
v___x_1249_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_);
v___x_1250_ = l_Lean_registerTraceClass(v___x_1247_, v___x_1248_, v___x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2____boxed(lean_object* v_a_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_();
return v_res_1252_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_PullLetDecls(uint8_t builtin) {
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
l_Lean_Compiler_LCNF_pullInstances = _init_l_Lean_Compiler_LCNF_pullInstances();
lean_mark_persistent(l_Lean_Compiler_LCNF_pullInstances);
res = l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_PullLetDecls(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_PullLetDecls(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_DependsOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PullLetDecls(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_PullLetDecls(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_PullLetDecls(builtin);
}
#ifdef __cplusplus
}
#endif
