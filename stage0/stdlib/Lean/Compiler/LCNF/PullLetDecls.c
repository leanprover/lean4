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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(uint8_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_264_ = lean_st_ref_set(v_a_239_, v___x_263_);
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
v___x_353_ = lean_st_ref_set(v_a_331_, v___x_352_);
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
v___x_395_ = lean_unsigned_to_nat(640u);
v___x_396_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__1));
v___x_397_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__0));
v___x_398_ = l_mkPanicMessageWithDecl(v___x_397_, v___x_396_, v___x_395_, v___x_394_, v___x_393_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0(lean_object* v_code_399_, uint8_t v___x_400_, lean_object* v_decl_401_, lean_object* v_type_402_, lean_object* v_params_403_, lean_object* v_k_404_, lean_object* v_value_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v___y_414_; lean_object* v___y_415_; uint8_t v___y_416_; lean_object* v___y_421_; lean_object* v___y_422_; uint8_t v___y_423_; lean_object* v_isCandidateFn_427_; lean_object* v_included_428_; lean_object* v___y_430_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_isCandidateFn_427_ = lean_ctor_get(v___y_406_, 0);
v_included_428_ = lean_ctor_get(v___y_406_, 1);
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_array_get_size(v_params_403_);
v___x_476_ = lean_nat_dec_lt(v___x_474_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_inc(v_included_428_);
lean_inc_ref(v_isCandidateFn_427_);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v_isCandidateFn_427_);
lean_ctor_set(v___x_477_, 1, v_included_428_);
v___x_478_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_value_405_, v___x_477_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec_ref(v___x_477_);
v___y_430_ = v___x_478_;
goto v___jp_429_;
}
else
{
uint8_t v___x_479_; 
v___x_479_ = lean_nat_dec_le(v___x_475_, v___x_475_);
if (v___x_479_ == 0)
{
if (v___x_476_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_inc(v_included_428_);
lean_inc_ref(v_isCandidateFn_427_);
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v_isCandidateFn_427_);
lean_ctor_set(v___x_480_, 1, v_included_428_);
v___x_481_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_value_405_, v___x_480_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec_ref(v___x_480_);
v___y_430_ = v___x_481_;
goto v___jp_429_;
}
else
{
size_t v___x_482_; size_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_482_ = ((size_t)0ULL);
v___x_483_ = lean_usize_of_nat(v___x_475_);
lean_inc(v_included_428_);
v___x_484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_403_, v___x_482_, v___x_483_, v_included_428_);
lean_inc_ref(v_isCandidateFn_427_);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v_isCandidateFn_427_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_value_405_, v___x_485_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec_ref(v___x_485_);
v___y_430_ = v___x_486_;
goto v___jp_429_;
}
}
else
{
size_t v___x_487_; size_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_487_ = ((size_t)0ULL);
v___x_488_ = lean_usize_of_nat(v___x_475_);
lean_inc(v_included_428_);
v___x_489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_403_, v___x_487_, v___x_488_, v_included_428_);
lean_inc_ref(v_isCandidateFn_427_);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v_isCandidateFn_427_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
v___x_491_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_value_405_, v___x_490_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec_ref(v___x_490_);
v___y_430_ = v___x_491_;
goto v___jp_429_;
}
}
v___jp_413_:
{
if (v___y_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec_ref(v_code_399_);
v___x_417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_417_, 0, v___y_414_);
lean_ctor_set(v___x_417_, 1, v___y_415_);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
else
{
lean_object* v___x_419_; 
lean_dec_ref(v___y_415_);
lean_dec_ref(v___y_414_);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v_code_399_);
return v___x_419_;
}
}
v___jp_420_:
{
if (v___y_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec_ref(v_code_399_);
v___x_424_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_424_, 0, v___y_421_);
lean_ctor_set(v___x_424_, 1, v___y_422_);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
else
{
lean_object* v___x_426_; 
lean_dec_ref(v___y_422_);
lean_dec_ref(v___y_421_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v_code_399_);
return v___x_426_;
}
}
v___jp_429_:
{
if (lean_obj_tag(v___y_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_432_; 
v_a_431_ = lean_ctor_get(v___y_430_, 0);
lean_inc(v_a_431_);
lean_dec_ref(v___y_430_);
v___x_432_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_400_, v_decl_401_, v_type_402_, v_params_403_, v_a_431_, v___y_409_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v_fvarId_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
lean_dec_ref(v___x_432_);
v_fvarId_434_ = lean_ctor_get(v_a_433_, 0);
lean_inc(v_fvarId_434_);
lean_inc(v_included_428_);
v___x_435_ = l_Lean_FVarIdSet_insert(v_included_428_, v_fvarId_434_);
lean_inc_ref(v_isCandidateFn_427_);
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v_isCandidateFn_427_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_k_404_, v___x_436_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec_ref(v___x_436_);
if (lean_obj_tag(v___x_437_) == 0)
{
switch(lean_obj_tag(v_code_399_))
{
case 1:
{
lean_object* v_a_438_; lean_object* v_decl_439_; lean_object* v_k_440_; size_t v___x_441_; size_t v___x_442_; uint8_t v___x_443_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref(v___x_437_);
v_decl_439_ = lean_ctor_get(v_code_399_, 0);
v_k_440_ = lean_ctor_get(v_code_399_, 1);
v___x_441_ = lean_ptr_addr(v_k_440_);
v___x_442_ = lean_ptr_addr(v_a_438_);
v___x_443_ = lean_usize_dec_eq(v___x_441_, v___x_442_);
if (v___x_443_ == 0)
{
v___y_414_ = v_a_433_;
v___y_415_ = v_a_438_;
v___y_416_ = v___x_443_;
goto v___jp_413_;
}
else
{
size_t v___x_444_; size_t v___x_445_; uint8_t v___x_446_; 
v___x_444_ = lean_ptr_addr(v_decl_439_);
v___x_445_ = lean_ptr_addr(v_a_433_);
v___x_446_ = lean_usize_dec_eq(v___x_444_, v___x_445_);
v___y_414_ = v_a_433_;
v___y_415_ = v_a_438_;
v___y_416_ = v___x_446_;
goto v___jp_413_;
}
}
case 2:
{
lean_object* v_a_447_; lean_object* v_decl_448_; lean_object* v_k_449_; size_t v___x_450_; size_t v___x_451_; uint8_t v___x_452_; 
v_a_447_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_447_);
lean_dec_ref(v___x_437_);
v_decl_448_ = lean_ctor_get(v_code_399_, 0);
v_k_449_ = lean_ctor_get(v_code_399_, 1);
v___x_450_ = lean_ptr_addr(v_k_449_);
v___x_451_ = lean_ptr_addr(v_a_447_);
v___x_452_ = lean_usize_dec_eq(v___x_450_, v___x_451_);
if (v___x_452_ == 0)
{
v___y_421_ = v_a_433_;
v___y_422_ = v_a_447_;
v___y_423_ = v___x_452_;
goto v___jp_420_;
}
else
{
size_t v___x_453_; size_t v___x_454_; uint8_t v___x_455_; 
v___x_453_ = lean_ptr_addr(v_decl_448_);
v___x_454_ = lean_ptr_addr(v_a_433_);
v___x_455_ = lean_usize_dec_eq(v___x_453_, v___x_454_);
v___y_421_ = v_a_433_;
v___y_422_ = v_a_447_;
v___y_423_ = v___x_455_;
goto v___jp_420_;
}
}
default: 
{
lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_464_; 
lean_dec(v_a_433_);
lean_dec_ref(v_code_399_);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v___x_437_, 0);
lean_dec(v_unused_465_);
v___x_457_ = v___x_437_;
v_isShared_458_ = v_isSharedCheck_464_;
goto v_resetjp_456_;
}
else
{
lean_dec(v___x_437_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_464_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_459_ = lean_obj_once(&l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__3, &l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__3_once, _init_l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__3);
v___x_460_ = l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2(v___x_459_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_460_);
v___x_462_ = v___x_457_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
else
{
lean_dec(v_a_433_);
lean_dec_ref(v_code_399_);
return v___x_437_;
}
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec_ref(v_k_404_);
lean_dec_ref(v_code_399_);
v_a_466_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_432_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_432_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
else
{
lean_dec_ref(v_k_404_);
lean_dec_ref(v_params_403_);
lean_dec_ref(v_type_402_);
lean_dec_ref(v_decl_401_);
lean_dec_ref(v_code_399_);
return v___y_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___boxed(lean_object* v_code_492_, lean_object* v___x_493_, lean_object* v_decl_494_, lean_object* v_type_495_, lean_object* v_params_496_, lean_object* v_k_497_, lean_object* v_value_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
uint8_t v___x_4728__boxed_506_; lean_object* v_res_507_; 
v___x_4728__boxed_506_ = lean_unbox(v___x_493_);
v_res_507_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0(v_code_492_, v___x_4728__boxed_506_, v_decl_494_, v_type_495_, v_params_496_, v_k_497_, v_value_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__1___boxed(lean_object* v___x_511_, lean_object* v_alts_512_, lean_object* v_typeName_513_, lean_object* v_resultType_514_, lean_object* v_discr_515_, lean_object* v_code_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__1(v___x_511_, v_alts_512_, v_typeName_513_, v_resultType_514_, v_discr_515_, v_code_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(lean_object* v_code_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_decl_534_; lean_object* v_k_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; 
switch(lean_obj_tag(v_code_525_))
{
case 4:
{
lean_object* v_cases_549_; lean_object* v_typeName_550_; lean_object* v_resultType_551_; lean_object* v_discr_552_; lean_object* v_alts_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v_cases_549_ = lean_ctor_get(v_code_525_, 0);
v_typeName_550_ = lean_ctor_get(v_cases_549_, 0);
v_resultType_551_ = lean_ctor_get(v_cases_549_, 1);
v_discr_552_ = lean_ctor_get(v_cases_549_, 2);
v_alts_553_ = lean_ctor_get(v_cases_549_, 3);
v___x_554_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___closed__1));
v___x_555_ = lean_name_eq(v_typeName_550_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___f_557_; lean_object* v___x_558_; 
lean_inc_ref(v_alts_553_);
lean_inc(v_discr_552_);
lean_inc_ref(v_resultType_551_);
lean_inc(v_typeName_550_);
v___x_556_ = lean_unsigned_to_nat(0u);
v___f_557_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__1___boxed), 13, 6);
lean_closure_set(v___f_557_, 0, v___x_556_);
lean_closure_set(v___f_557_, 1, v_alts_553_);
lean_closure_set(v___f_557_, 2, v_typeName_550_);
lean_closure_set(v___f_557_, 3, v_resultType_551_);
lean_closure_set(v___f_557_, 4, v_discr_552_);
lean_closure_set(v___f_557_, 5, v_code_525_);
v___x_558_ = l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint(v___f_557_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
return v___x_558_;
}
else
{
lean_object* v___x_559_; 
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v_code_525_);
return v___x_559_;
}
}
case 0:
{
lean_object* v_decl_560_; lean_object* v_k_561_; lean_object* v___x_562_; 
v_decl_560_ = lean_ctor_get(v_code_525_, 0);
v_k_561_ = lean_ctor_get(v_code_525_, 1);
lean_inc_ref(v_decl_560_);
v___x_562_ = l_Lean_Compiler_LCNF_PullLetDecls_shouldPull(v_decl_560_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; uint8_t v___x_564_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_563_);
lean_dec_ref(v___x_562_);
v___x_564_ = lean_unbox(v_a_563_);
lean_dec(v_a_563_);
if (v___x_564_ == 0)
{
lean_object* v_fvarId_565_; lean_object* v_isCandidateFn_566_; lean_object* v_included_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_fvarId_565_ = lean_ctor_get(v_decl_560_, 0);
v_isCandidateFn_566_ = lean_ctor_get(v_a_526_, 0);
v_included_567_ = lean_ctor_get(v_a_526_, 1);
lean_inc(v_fvarId_565_);
lean_inc(v_included_567_);
v___x_568_ = l_Lean_FVarIdSet_insert(v_included_567_, v_fvarId_565_);
lean_inc_ref(v_isCandidateFn_566_);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v_isCandidateFn_566_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
lean_inc_ref(v_k_561_);
v___x_570_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_k_561_, v___x_569_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
lean_dec_ref(v___x_569_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_593_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_593_ == 0)
{
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_593_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_593_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
size_t v___x_575_; size_t v___x_576_; uint8_t v___x_577_; 
v___x_575_ = lean_ptr_addr(v_k_561_);
v___x_576_ = lean_ptr_addr(v_a_571_);
v___x_577_ = lean_usize_dec_eq(v___x_575_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_587_; 
lean_inc_ref(v_decl_560_);
v_isSharedCheck_587_ = !lean_is_exclusive(v_code_525_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; lean_object* v_unused_589_; 
v_unused_588_ = lean_ctor_get(v_code_525_, 1);
lean_dec(v_unused_588_);
v_unused_589_ = lean_ctor_get(v_code_525_, 0);
lean_dec(v_unused_589_);
v___x_579_ = v_code_525_;
v_isShared_580_ = v_isSharedCheck_587_;
goto v_resetjp_578_;
}
else
{
lean_dec(v_code_525_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_587_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 1, v_a_571_);
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_decl_560_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_a_571_);
v___x_582_ = v_reuseFailAlloc_586_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_584_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_582_);
v___x_584_ = v___x_573_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
else
{
lean_object* v___x_591_; 
lean_dec(v_a_571_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v_code_525_);
v___x_591_ = v___x_573_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_code_525_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
else
{
lean_dec_ref(v_code_525_);
return v___x_570_;
}
}
else
{
lean_inc_ref(v_k_561_);
lean_dec_ref(v_code_525_);
v_code_525_ = v_k_561_;
goto _start;
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec_ref(v_code_525_);
v_a_595_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_562_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_562_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
case 1:
{
lean_object* v_decl_603_; lean_object* v_k_604_; 
v_decl_603_ = lean_ctor_get(v_code_525_, 0);
v_k_604_ = lean_ctor_get(v_code_525_, 1);
lean_inc_ref(v_k_604_);
lean_inc_ref(v_decl_603_);
v_decl_534_ = v_decl_603_;
v_k_535_ = v_k_604_;
v___y_536_ = v_a_526_;
v___y_537_ = v_a_527_;
v___y_538_ = v_a_528_;
v___y_539_ = v_a_529_;
v___y_540_ = v_a_530_;
v___y_541_ = v_a_531_;
goto v___jp_533_;
}
case 2:
{
lean_object* v_decl_605_; lean_object* v_k_606_; 
v_decl_605_ = lean_ctor_get(v_code_525_, 0);
v_k_606_ = lean_ctor_get(v_code_525_, 1);
lean_inc_ref(v_k_606_);
lean_inc_ref(v_decl_605_);
v_decl_534_ = v_decl_605_;
v_k_535_ = v_k_606_;
v___y_536_ = v_a_526_;
v___y_537_ = v_a_527_;
v___y_538_ = v_a_528_;
v___y_539_ = v_a_529_;
v___y_540_ = v_a_530_;
v___y_541_ = v_a_531_;
goto v___jp_533_;
}
default: 
{
lean_object* v___x_607_; 
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v_code_525_);
return v___x_607_;
}
}
v___jp_533_:
{
lean_object* v_params_542_; lean_object* v_type_543_; lean_object* v_value_544_; uint8_t v___x_545_; lean_object* v___x_546_; lean_object* v___f_547_; lean_object* v___x_548_; 
v_params_542_ = lean_ctor_get(v_decl_534_, 2);
lean_inc_ref(v_params_542_);
v_type_543_ = lean_ctor_get(v_decl_534_, 3);
lean_inc_ref(v_type_543_);
v_value_544_ = lean_ctor_get(v_decl_534_, 4);
lean_inc_ref(v_value_544_);
v___x_545_ = 0;
v___x_546_ = lean_box(v___x_545_);
v___f_547_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___boxed), 14, 7);
lean_closure_set(v___f_547_, 0, v_code_525_);
lean_closure_set(v___f_547_, 1, v___x_546_);
lean_closure_set(v___f_547_, 2, v_decl_534_);
lean_closure_set(v___f_547_, 3, v_type_543_);
lean_closure_set(v___f_547_, 4, v_params_542_);
lean_closure_set(v___f_547_, 5, v_k_535_);
lean_closure_set(v___f_547_, 6, v_value_544_);
v___x_548_ = l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint(v___f_547_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullAlt(lean_object* v_alt_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_){
_start:
{
lean_object* v___y_617_; 
if (lean_obj_tag(v_alt_608_) == 0)
{
lean_object* v_params_635_; lean_object* v_code_636_; lean_object* v_isCandidateFn_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_params_635_ = lean_ctor_get(v_alt_608_, 1);
v_code_636_ = lean_ctor_get(v_alt_608_, 2);
v_isCandidateFn_637_ = lean_ctor_get(v_a_609_, 0);
v___x_638_ = lean_box(1);
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = lean_array_get_size(v_params_635_);
v___x_641_ = lean_nat_dec_lt(v___x_639_, v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; 
lean_inc_ref(v_isCandidateFn_637_);
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v_isCandidateFn_637_);
lean_ctor_set(v___x_642_, 1, v___x_638_);
lean_inc_ref(v_code_636_);
v___x_643_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_code_636_, v___x_642_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
lean_dec_ref(v___x_642_);
v___y_617_ = v___x_643_;
goto v___jp_616_;
}
else
{
uint8_t v___x_644_; 
v___x_644_ = lean_nat_dec_le(v___x_640_, v___x_640_);
if (v___x_644_ == 0)
{
if (v___x_641_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; 
lean_inc_ref(v_isCandidateFn_637_);
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v_isCandidateFn_637_);
lean_ctor_set(v___x_645_, 1, v___x_638_);
lean_inc_ref(v_code_636_);
v___x_646_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_code_636_, v___x_645_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
lean_dec_ref(v___x_645_);
v___y_617_ = v___x_646_;
goto v___jp_616_;
}
else
{
size_t v___x_647_; size_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_647_ = ((size_t)0ULL);
v___x_648_ = lean_usize_of_nat(v___x_640_);
v___x_649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_635_, v___x_647_, v___x_648_, v___x_638_);
lean_inc_ref(v_isCandidateFn_637_);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v_isCandidateFn_637_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
lean_inc_ref(v_code_636_);
v___x_651_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_code_636_, v___x_650_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
lean_dec_ref(v___x_650_);
v___y_617_ = v___x_651_;
goto v___jp_616_;
}
}
else
{
size_t v___x_652_; size_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_652_ = ((size_t)0ULL);
v___x_653_ = lean_usize_of_nat(v___x_640_);
v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_635_, v___x_652_, v___x_653_, v___x_638_);
lean_inc_ref(v_isCandidateFn_637_);
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v_isCandidateFn_637_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
lean_inc_ref(v_code_636_);
v___x_656_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_code_636_, v___x_655_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
lean_dec_ref(v___x_655_);
v___y_617_ = v___x_656_;
goto v___jp_616_;
}
}
}
else
{
lean_object* v_code_657_; lean_object* v_isCandidateFn_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v_code_657_ = lean_ctor_get(v_alt_608_, 0);
v_isCandidateFn_658_ = lean_ctor_get(v_a_609_, 0);
v___x_659_ = lean_box(1);
lean_inc_ref(v_isCandidateFn_658_);
v___x_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_660_, 0, v_isCandidateFn_658_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
lean_inc_ref(v_code_657_);
v___x_661_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_code_657_, v___x_660_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
lean_dec_ref(v___x_660_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_670_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_670_ == 0)
{
v___x_664_ = v___x_661_;
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_666_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_608_, v_a_662_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_666_);
v___x_668_ = v___x_664_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec_ref(v_alt_608_);
v_a_671_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_661_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_661_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
v___jp_616_:
{
if (lean_obj_tag(v___y_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_626_; 
v_a_618_ = lean_ctor_get(v___y_617_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___y_617_);
if (v_isSharedCheck_626_ == 0)
{
v___x_620_ = v___y_617_;
v_isShared_621_ = v_isSharedCheck_626_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___y_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_626_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_622_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_608_, v_a_618_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_622_);
v___x_624_ = v___x_620_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec_ref(v_alt_608_);
v_a_627_ = lean_ctor_get(v___y_617_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___y_617_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___y_617_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___y_617_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__3(lean_object* v_i_679_, lean_object* v_as_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_688_ = lean_array_get_size(v_as_680_);
v___x_689_ = lean_nat_dec_lt(v_i_679_, v___x_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; 
lean_dec(v_i_679_);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v_as_680_);
return v___x_690_;
}
else
{
lean_object* v_a_691_; lean_object* v___x_692_; 
v_a_691_ = lean_array_fget_borrowed(v_as_680_, v_i_679_);
lean_inc(v_a_691_);
v___x_692_ = l_Lean_Compiler_LCNF_PullLetDecls_pullAlt(v_a_691_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; size_t v___x_694_; size_t v___x_695_; uint8_t v___x_696_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref(v___x_692_);
v___x_694_ = lean_ptr_addr(v_a_691_);
v___x_695_ = lean_ptr_addr(v_a_693_);
v___x_696_ = lean_usize_dec_eq(v___x_694_, v___x_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = lean_unsigned_to_nat(1u);
v___x_698_ = lean_nat_add(v_i_679_, v___x_697_);
v___x_699_ = lean_array_fset(v_as_680_, v_i_679_, v_a_693_);
lean_dec(v_i_679_);
v_i_679_ = v___x_698_;
v_as_680_ = v___x_699_;
goto _start;
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; 
lean_dec(v_a_693_);
v___x_701_ = lean_unsigned_to_nat(1u);
v___x_702_ = lean_nat_add(v_i_679_, v___x_701_);
lean_dec(v_i_679_);
v_i_679_ = v___x_702_;
goto _start;
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec_ref(v_as_680_);
lean_dec(v_i_679_);
v_a_704_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_692_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_692_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__1(lean_object* v___x_712_, lean_object* v_alts_713_, lean_object* v_typeName_714_, lean_object* v_resultType_715_, lean_object* v_discr_716_, lean_object* v_code_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; 
lean_inc_ref(v_alts_713_);
v___x_725_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__3(v___x_712_, v_alts_713_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_741_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_741_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_741_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_741_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
size_t v___x_730_; size_t v___x_731_; uint8_t v___x_732_; 
v___x_730_ = lean_ptr_addr(v_alts_713_);
lean_dec_ref(v_alts_713_);
v___x_731_ = lean_ptr_addr(v_a_726_);
v___x_732_ = lean_usize_dec_eq(v___x_730_, v___x_731_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
lean_dec_ref(v_code_717_);
v___x_733_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_733_, 0, v_typeName_714_);
lean_ctor_set(v___x_733_, 1, v_resultType_715_);
lean_ctor_set(v___x_733_, 2, v_discr_716_);
lean_ctor_set(v___x_733_, 3, v_a_726_);
v___x_734_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_734_);
v___x_736_ = v___x_728_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
else
{
lean_object* v___x_739_; 
lean_dec(v_a_726_);
lean_dec(v_discr_716_);
lean_dec_ref(v_resultType_715_);
lean_dec(v_typeName_714_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v_code_717_);
v___x_739_ = v___x_728_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_code_717_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec_ref(v_code_717_);
lean_dec(v_discr_716_);
lean_dec_ref(v_resultType_715_);
lean_dec(v_typeName_714_);
lean_dec_ref(v_alts_713_);
v_a_742_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_725_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_725_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__3___boxed(lean_object* v_i_750_, lean_object* v_as_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__3(v_i_750_, v_as_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___boxed(lean_object* v_code_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_code_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullAlt___boxed(lean_object* v_alt_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Compiler_LCNF_PullLetDecls_pullAlt(v_alt_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg(lean_object* v_x_778_, lean_object* v_isCandidateFn_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_785_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint___closed__0));
v___x_786_ = lean_st_mk_ref(v___x_785_);
v___x_787_ = lean_box(1);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v_isCandidateFn_779_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
lean_inc(v_a_783_);
lean_inc_ref(v_a_782_);
lean_inc(v_a_781_);
lean_inc_ref(v_a_780_);
lean_inc(v___x_786_);
v___x_789_ = lean_apply_7(v_x_778_, v___x_788_, v___x_786_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, lean_box(0));
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_798_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_798_ == 0)
{
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_798_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_798_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_794_ = lean_st_ref_get(v___x_786_);
lean_dec(v___x_786_);
lean_dec(v___x_794_);
if (v_isShared_793_ == 0)
{
v___x_796_ = v___x_792_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_790_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
else
{
lean_dec(v___x_786_);
return v___x_789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg___boxed(lean_object* v_x_799_, lean_object* v_isCandidateFn_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg(v_x_799_, v_isCandidateFn_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_PullM_run(lean_object* v_00_u03b1_807_, lean_object* v_x_808_, lean_object* v_isCandidateFn_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg(v_x_808_, v_isCandidateFn_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___boxed(lean_object* v_00_u03b1_816_, lean_object* v_x_817_, lean_object* v_isCandidateFn_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_Compiler_LCNF_PullLetDecls_PullM_run(v_00_u03b1_816_, v_x_817_, v_isCandidateFn_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(lean_object* v_f_825_, lean_object* v_v_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
if (lean_obj_tag(v_v_826_) == 0)
{
lean_object* v_code_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_858_; 
v_code_834_ = lean_ctor_get(v_v_826_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v_v_826_);
if (v_isSharedCheck_858_ == 0)
{
v___x_836_ = v_v_826_;
v_isShared_837_ = v_isSharedCheck_858_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_code_834_);
lean_dec(v_v_826_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_858_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; 
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
lean_inc(v___y_828_);
lean_inc_ref(v___y_827_);
v___x_838_ = lean_apply_8(v_f_825_, v_code_834_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, lean_box(0));
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_849_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_849_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_849_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_849_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v_a_839_);
v___x_844_ = v___x_836_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_848_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_846_; 
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_844_);
v___x_846_ = v___x_841_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_del_object(v___x_836_);
v_a_850_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_838_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_838_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
else
{
lean_object* v___x_859_; 
lean_dec_ref(v_f_825_);
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v_v_826_);
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg___boxed(lean_object* v_f_860_, lean_object* v_v_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(v_f_860_, v_v_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0(uint8_t v_pu_870_, lean_object* v_f_871_, lean_object* v_v_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(v_f_871_, v_v_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___boxed(lean_object* v_pu_881_, lean_object* v_f_882_, lean_object* v_v_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
uint8_t v_pu_boxed_891_; lean_object* v_res_892_; 
v_pu_boxed_891_ = lean_unbox(v_pu_881_);
v_res_892_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0(v_pu_boxed_891_, v_f_882_, v_v_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0(lean_object* v___x_894_, lean_object* v_value_895_, lean_object* v_toSignature_896_, uint8_t v_recursive_897_, lean_object* v_inlineAttr_x3f_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(v___x_894_, v_value_895_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_907_);
lean_dec_ref(v___x_906_);
v___x_908_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0___closed__0));
v___x_909_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(v___x_908_, v_a_907_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_918_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_918_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_914_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_914_, 0, v_toSignature_896_);
lean_ctor_set(v___x_914_, 1, v_a_910_);
lean_ctor_set(v___x_914_, 2, v_inlineAttr_x3f_898_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*3, v_recursive_897_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_914_);
v___x_916_ = v___x_912_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec(v_inlineAttr_x3f_898_);
lean_dec_ref(v_toSignature_896_);
v_a_919_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_909_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_909_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec(v_inlineAttr_x3f_898_);
lean_dec_ref(v_toSignature_896_);
v_a_927_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_906_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_906_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0___boxed(lean_object* v___x_935_, lean_object* v_value_936_, lean_object* v_toSignature_937_, lean_object* v_recursive_938_, lean_object* v_inlineAttr_x3f_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
uint8_t v_recursive_boxed_947_; lean_object* v_res_948_; 
v_recursive_boxed_947_ = lean_unbox(v_recursive_938_);
v_res_948_ = l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0(v___x_935_, v_value_936_, v_toSignature_937_, v_recursive_boxed_947_, v_inlineAttr_x3f_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__1(lean_object* v_params_949_, lean_object* v___f_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_isCandidateFn_958_; lean_object* v_included_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_isCandidateFn_958_ = lean_ctor_get(v___y_951_, 0);
v_included_959_ = lean_ctor_get(v___y_951_, 1);
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_961_ = lean_array_get_size(v_params_949_);
v___x_962_ = lean_nat_dec_lt(v___x_960_, v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
v___x_963_ = lean_apply_7(v___f_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, lean_box(0));
return v___x_963_;
}
else
{
uint8_t v___x_964_; 
v___x_964_ = lean_nat_dec_le(v___x_961_, v___x_961_);
if (v___x_964_ == 0)
{
if (v___x_962_ == 0)
{
lean_object* v___x_965_; 
v___x_965_ = lean_apply_7(v___f_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, lean_box(0));
return v___x_965_;
}
else
{
lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_976_; 
lean_inc(v_included_959_);
lean_inc_ref(v_isCandidateFn_958_);
v_isSharedCheck_976_ = !lean_is_exclusive(v___y_951_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; lean_object* v_unused_978_; 
v_unused_977_ = lean_ctor_get(v___y_951_, 1);
lean_dec(v_unused_977_);
v_unused_978_ = lean_ctor_get(v___y_951_, 0);
lean_dec(v_unused_978_);
v___x_967_ = v___y_951_;
v_isShared_968_ = v_isSharedCheck_976_;
goto v_resetjp_966_;
}
else
{
lean_dec(v___y_951_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_976_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
size_t v___x_969_; size_t v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_969_ = ((size_t)0ULL);
v___x_970_ = lean_usize_of_nat(v___x_961_);
v___x_971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_949_, v___x_969_, v___x_970_, v_included_959_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 1, v___x_971_);
v___x_973_ = v___x_967_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_isCandidateFn_958_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v___x_971_);
v___x_973_ = v_reuseFailAlloc_975_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; 
v___x_974_ = lean_apply_7(v___f_950_, v___x_973_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, lean_box(0));
return v___x_974_;
}
}
}
}
else
{
lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_989_; 
lean_inc(v_included_959_);
lean_inc_ref(v_isCandidateFn_958_);
v_isSharedCheck_989_ = !lean_is_exclusive(v___y_951_);
if (v_isSharedCheck_989_ == 0)
{
lean_object* v_unused_990_; lean_object* v_unused_991_; 
v_unused_990_ = lean_ctor_get(v___y_951_, 1);
lean_dec(v_unused_990_);
v_unused_991_ = lean_ctor_get(v___y_951_, 0);
lean_dec(v_unused_991_);
v___x_980_ = v___y_951_;
v_isShared_981_ = v_isSharedCheck_989_;
goto v_resetjp_979_;
}
else
{
lean_dec(v___y_951_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_989_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
size_t v___x_982_; size_t v___x_983_; lean_object* v___x_984_; lean_object* v___x_986_; 
v___x_982_ = ((size_t)0ULL);
v___x_983_ = lean_usize_of_nat(v___x_961_);
v___x_984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_949_, v___x_982_, v___x_983_, v_included_959_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 1, v___x_984_);
v___x_986_ = v___x_980_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_isCandidateFn_958_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v___x_984_);
v___x_986_ = v_reuseFailAlloc_988_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_987_; 
v___x_987_ = lean_apply_7(v___f_950_, v___x_986_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, lean_box(0));
return v___x_987_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__1___boxed(lean_object* v_params_992_, lean_object* v___f_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__1(v_params_992_, v___f_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
lean_dec_ref(v_params_992_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls(lean_object* v_decl_1003_, lean_object* v_isCandidateFn_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_toSignature_1010_; lean_object* v_value_1011_; uint8_t v_recursive_1012_; lean_object* v_inlineAttr_x3f_1013_; lean_object* v_params_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___f_1017_; lean_object* v___f_1018_; lean_object* v___x_1019_; 
v_toSignature_1010_ = lean_ctor_get(v_decl_1003_, 0);
lean_inc_ref(v_toSignature_1010_);
v_value_1011_ = lean_ctor_get(v_decl_1003_, 1);
lean_inc_ref(v_value_1011_);
v_recursive_1012_ = lean_ctor_get_uint8(v_decl_1003_, sizeof(void*)*3);
v_inlineAttr_x3f_1013_ = lean_ctor_get(v_decl_1003_, 2);
lean_inc(v_inlineAttr_x3f_1013_);
lean_dec_ref(v_decl_1003_);
v_params_1014_ = lean_ctor_get(v_toSignature_1010_, 3);
lean_inc_ref(v_params_1014_);
v___x_1015_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_pullLetDecls___closed__0));
v___x_1016_ = lean_box(v_recursive_1012_);
v___f_1017_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1017_, 0, v___x_1015_);
lean_closure_set(v___f_1017_, 1, v_value_1011_);
lean_closure_set(v___f_1017_, 2, v_toSignature_1010_);
lean_closure_set(v___f_1017_, 3, v___x_1016_);
lean_closure_set(v___f_1017_, 4, v_inlineAttr_x3f_1013_);
v___f_1018_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__1___boxed), 9, 2);
lean_closure_set(v___f_1018_, 0, v_params_1014_);
lean_closure_set(v___f_1018_, 1, v___f_1017_);
v___x_1019_ = l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg(v___f_1018_, v_isCandidateFn_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___boxed(lean_object* v_decl_1020_, lean_object* v_isCandidateFn_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_Compiler_LCNF_Decl_pullLetDecls(v_decl_1020_, v_isCandidateFn_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
return v_res_1027_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg(lean_object* v_k_1028_, lean_object* v_t_1029_){
_start:
{
if (lean_obj_tag(v_t_1029_) == 0)
{
lean_object* v_k_1030_; lean_object* v_l_1031_; lean_object* v_r_1032_; uint8_t v___x_1033_; 
v_k_1030_ = lean_ctor_get(v_t_1029_, 1);
v_l_1031_ = lean_ctor_get(v_t_1029_, 3);
v_r_1032_ = lean_ctor_get(v_t_1029_, 4);
v___x_1033_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1028_, v_k_1030_);
switch(v___x_1033_)
{
case 0:
{
v_t_1029_ = v_l_1031_;
goto _start;
}
case 1:
{
uint8_t v___x_1035_; 
v___x_1035_ = 1;
return v___x_1035_;
}
default: 
{
v_t_1029_ = v_r_1032_;
goto _start;
}
}
}
else
{
uint8_t v___x_1037_; 
v___x_1037_ = 0;
return v___x_1037_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg___boxed(lean_object* v_k_1038_, lean_object* v_t_1039_){
_start:
{
uint8_t v_res_1040_; lean_object* v_r_1041_; 
v_res_1040_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg(v_k_1038_, v_t_1039_);
lean_dec(v_t_1039_);
lean_dec(v_k_1038_);
v_r_1041_ = lean_box(v_res_1040_);
return v_r_1041_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1(lean_object* v_as_1042_, size_t v_i_1043_, size_t v_stop_1044_){
_start:
{
uint8_t v___x_1045_; 
v___x_1045_ = lean_usize_dec_eq(v_i_1043_, v_stop_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v___x_1046_ = lean_array_uget_borrowed(v_as_1042_, v_i_1043_);
v___x_1047_ = lean_box(0);
v___x_1048_ = l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(v___x_1046_, v___x_1047_);
if (v___x_1048_ == 0)
{
size_t v___x_1049_; size_t v___x_1050_; 
v___x_1049_ = ((size_t)1ULL);
v___x_1050_ = lean_usize_add(v_i_1043_, v___x_1049_);
v_i_1043_ = v___x_1050_;
goto _start;
}
else
{
return v___x_1048_;
}
}
else
{
uint8_t v___x_1052_; 
v___x_1052_ = 0;
return v___x_1052_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1___boxed(lean_object* v_as_1053_, lean_object* v_i_1054_, lean_object* v_stop_1055_){
_start:
{
size_t v_i_boxed_1056_; size_t v_stop_boxed_1057_; uint8_t v_res_1058_; lean_object* v_r_1059_; 
v_i_boxed_1056_ = lean_unbox_usize(v_i_1054_);
lean_dec(v_i_1054_);
v_stop_boxed_1057_ = lean_unbox_usize(v_stop_1055_);
lean_dec(v_stop_1055_);
v_res_1058_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1(v_as_1053_, v_i_boxed_1056_, v_stop_boxed_1057_);
lean_dec_ref(v_as_1053_);
v_r_1059_ = lean_box(v_res_1058_);
return v_r_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullInstances___lam__0(lean_object* v_letDecl_1060_, lean_object* v_candidates_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_type_1067_; lean_object* v_value_1068_; lean_object* v___y_1070_; lean_object* v___y_1102_; 
v_type_1067_ = lean_ctor_get(v_letDecl_1060_, 2);
v_value_1068_ = lean_ctor_get(v_letDecl_1060_, 3);
if (lean_obj_tag(v_value_1068_) == 3)
{
lean_object* v_args_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v_args_1113_ = lean_ctor_get(v_value_1068_, 2);
v___x_1114_ = lean_unsigned_to_nat(0u);
v___x_1115_ = lean_array_get_size(v_args_1113_);
v___x_1116_ = lean_nat_dec_lt(v___x_1114_, v___x_1115_);
if (v___x_1116_ == 0)
{
v___y_1102_ = v___y_1065_;
goto v___jp_1101_;
}
else
{
if (v___x_1116_ == 0)
{
v___y_1102_ = v___y_1065_;
goto v___jp_1101_;
}
else
{
size_t v___x_1117_; size_t v___x_1118_; uint8_t v___x_1119_; 
v___x_1117_ = ((size_t)0ULL);
v___x_1118_ = lean_usize_of_nat(v___x_1115_);
v___x_1119_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1(v_args_1113_, v___x_1117_, v___x_1118_);
if (v___x_1119_ == 0)
{
v___y_1102_ = v___y_1065_;
goto v___jp_1101_;
}
else
{
uint8_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1120_ = 0;
v___x_1121_ = lean_box(v___x_1120_);
v___x_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
return v___x_1122_;
}
}
}
}
else
{
v___y_1102_ = v___y_1065_;
goto v___jp_1101_;
}
v___jp_1069_:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_1067_, v___y_1070_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1092_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1074_ = v___x_1071_;
v_isShared_1075_ = v_isSharedCheck_1092_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1092_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
if (lean_obj_tag(v_a_1072_) == 0)
{
if (lean_obj_tag(v_value_1068_) == 2)
{
lean_object* v_struct_1076_; uint8_t v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v_struct_1076_ = lean_ctor_get(v_value_1068_, 2);
v___x_1077_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg(v_struct_1076_, v_candidates_1061_);
v___x_1078_ = lean_box(v___x_1077_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v___x_1078_);
v___x_1080_ = v___x_1074_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
else
{
uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1082_ = 0;
v___x_1083_ = lean_box(v___x_1082_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v___x_1083_);
v___x_1085_ = v___x_1074_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
else
{
uint8_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
lean_dec_ref(v_a_1072_);
v___x_1087_ = 1;
v___x_1088_ = lean_box(v___x_1087_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v___x_1088_);
v___x_1090_ = v___x_1074_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_a_1093_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1071_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1071_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
v___jp_1101_:
{
if (lean_obj_tag(v_value_1068_) == 4)
{
lean_object* v_args_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v_args_1103_ = lean_ctor_get(v_value_1068_, 1);
v___x_1104_ = lean_unsigned_to_nat(0u);
v___x_1105_ = lean_array_get_size(v_args_1103_);
v___x_1106_ = lean_nat_dec_lt(v___x_1104_, v___x_1105_);
if (v___x_1106_ == 0)
{
v___y_1070_ = v___y_1102_;
goto v___jp_1069_;
}
else
{
if (v___x_1106_ == 0)
{
v___y_1070_ = v___y_1102_;
goto v___jp_1069_;
}
else
{
size_t v___x_1107_; size_t v___x_1108_; uint8_t v___x_1109_; 
v___x_1107_ = ((size_t)0ULL);
v___x_1108_ = lean_usize_of_nat(v___x_1105_);
v___x_1109_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1(v_args_1103_, v___x_1107_, v___x_1108_);
if (v___x_1109_ == 0)
{
v___y_1070_ = v___y_1102_;
goto v___jp_1069_;
}
else
{
uint8_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = 0;
v___x_1111_ = lean_box(v___x_1110_);
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
return v___x_1112_;
}
}
}
}
else
{
v___y_1070_ = v___y_1102_;
goto v___jp_1069_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullInstances___lam__0___boxed(lean_object* v_letDecl_1123_, lean_object* v_candidates_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_Compiler_LCNF_Decl_pullInstances___lam__0(v_letDecl_1123_, v_candidates_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v_candidates_1124_);
lean_dec_ref(v_letDecl_1123_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullInstances(lean_object* v_decl_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v___f_1138_; lean_object* v___x_1139_; 
v___f_1138_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_pullInstances___closed__0));
v___x_1139_ = l_Lean_Compiler_LCNF_Decl_pullLetDecls(v_decl_1132_, v___f_1138_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullInstances___boxed(lean_object* v_decl_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_Compiler_LCNF_Decl_pullInstances(v_decl_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
return v_res_1146_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0(lean_object* v_00_u03b2_1147_, lean_object* v_k_1148_, lean_object* v_t_1149_){
_start:
{
uint8_t v___x_1150_; 
v___x_1150_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg(v_k_1148_, v_t_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___boxed(lean_object* v_00_u03b2_1151_, lean_object* v_k_1152_, lean_object* v_t_1153_){
_start:
{
uint8_t v_res_1154_; lean_object* v_r_1155_; 
v_res_1154_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0(v_00_u03b2_1151_, v_k_1152_, v_t_1153_);
lean_dec(v_t_1153_);
lean_dec(v_k_1152_);
v_r_1155_ = lean_box(v_res_1154_);
return v_r_1155_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullInstances___closed__3(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1160_ = lean_unsigned_to_nat(0u);
v___x_1161_ = ((lean_object*)(l_Lean_Compiler_LCNF_pullInstances___closed__2));
v___x_1162_ = 0;
v___x_1163_ = ((lean_object*)(l_Lean_Compiler_LCNF_pullInstances___closed__1));
v___x_1164_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1163_, v___x_1162_, v___x_1161_, v___x_1160_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullInstances(void){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_obj_once(&l_Lean_Compiler_LCNF_pullInstances___closed__3, &l_Lean_Compiler_LCNF_pullInstances___closed__3_once, _init_l_Lean_Compiler_LCNF_pullInstances___closed__3);
return v___x_1165_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = lean_unsigned_to_nat(3825914912u);
v___x_1222_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_));
v___x_1223_ = l_Lean_Name_num___override(v___x_1222_, v___x_1221_);
return v___x_1223_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_));
v___x_1226_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_);
v___x_1227_ = l_Lean_Name_str___override(v___x_1226_, v___x_1225_);
return v___x_1227_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1229_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_));
v___x_1230_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_);
v___x_1231_ = l_Lean_Name_str___override(v___x_1230_, v___x_1229_);
return v___x_1231_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1232_ = lean_unsigned_to_nat(2u);
v___x_1233_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_);
v___x_1234_ = l_Lean_Name_num___override(v___x_1233_, v___x_1232_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1236_; uint8_t v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1236_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_));
v___x_1237_ = 1;
v___x_1238_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_);
v___x_1239_ = l_Lean_registerTraceClass(v___x_1236_, v___x_1237_, v___x_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2____boxed(lean_object* v_a_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_();
return v_res_1241_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_PullLetDecls(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
