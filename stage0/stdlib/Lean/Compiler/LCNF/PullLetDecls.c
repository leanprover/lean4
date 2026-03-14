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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* v_isCandidateFn_10_; lean_object* v_included_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_20_; 
v_isCandidateFn_10_ = lean_ctor_get(v_a_3_, 0);
v_included_11_ = lean_ctor_get(v_a_3_, 1);
v_isSharedCheck_20_ = !lean_is_exclusive(v_a_3_);
if (v_isSharedCheck_20_ == 0)
{
v___x_13_ = v_a_3_;
v_isShared_14_ = v_isSharedCheck_20_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_included_11_);
lean_inc(v_isCandidateFn_10_);
lean_dec(v_a_3_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_20_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
v___x_15_ = l_Lean_FVarIdSet_insert(v_included_11_, v_fvarId_1_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_19_; 
v_reuseFailAlloc_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_19_, 0, v_isCandidateFn_10_);
lean_ctor_set(v_reuseFailAlloc_19_, 1, v___x_15_);
v___x_17_ = v_reuseFailAlloc_19_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
lean_object* v___x_18_; 
v___x_18_ = lean_apply_7(v_x_2_, v___x_17_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, lean_box(0));
return v___x_18_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withFVar___redArg___boxed(lean_object* v_fvarId_21_, lean_object* v_x_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Compiler_LCNF_PullLetDecls_withFVar___redArg(v_fvarId_21_, v_x_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withFVar(lean_object* v_00_u03b1_31_, lean_object* v_fvarId_32_, lean_object* v_x_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_isCandidateFn_41_; lean_object* v_included_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_51_; 
v_isCandidateFn_41_ = lean_ctor_get(v_a_34_, 0);
v_included_42_ = lean_ctor_get(v_a_34_, 1);
v_isSharedCheck_51_ = !lean_is_exclusive(v_a_34_);
if (v_isSharedCheck_51_ == 0)
{
v___x_44_ = v_a_34_;
v_isShared_45_ = v_isSharedCheck_51_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_included_42_);
lean_inc(v_isCandidateFn_41_);
lean_dec(v_a_34_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_51_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_46_; lean_object* v___x_48_; 
v___x_46_ = l_Lean_FVarIdSet_insert(v_included_42_, v_fvarId_32_);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 1, v___x_46_);
v___x_48_ = v___x_44_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_isCandidateFn_41_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v___x_46_);
v___x_48_ = v_reuseFailAlloc_50_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
lean_object* v___x_49_; 
v___x_49_ = lean_apply_7(v_x_33_, v___x_48_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, lean_box(0));
return v___x_49_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withFVar___boxed(lean_object* v_00_u03b1_52_, lean_object* v_fvarId_53_, lean_object* v_x_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Compiler_LCNF_PullLetDecls_withFVar(v_00_u03b1_52_, v_fvarId_53_, v_x_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___lam__0(lean_object* v_x1_63_, lean_object* v_x2_64_){
_start:
{
lean_object* v_fvarId_65_; lean_object* v___x_66_; 
v_fvarId_65_ = lean_ctor_get(v_x2_64_, 0);
lean_inc(v_fvarId_65_);
lean_dec_ref(v_x2_64_);
v___x_66_ = l_Lean_FVarIdSet_insert(v_x1_63_, v_fvarId_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg(lean_object* v_ps_87_, lean_object* v_x_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v_isCandidateFn_96_; lean_object* v_included_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v_isCandidateFn_96_ = lean_ctor_get(v_a_89_, 0);
v_included_97_ = lean_ctor_get(v_a_89_, 1);
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_array_get_size(v_ps_87_);
v___x_100_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__9));
v___x_101_ = lean_nat_dec_lt(v___x_98_, v___x_99_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
lean_dec_ref(v_ps_87_);
v___x_102_ = lean_apply_7(v_x_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, lean_box(0));
return v___x_102_;
}
else
{
lean_object* v___f_103_; uint8_t v___x_104_; 
v___f_103_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__10));
v___x_104_ = lean_nat_dec_le(v___x_99_, v___x_99_);
if (v___x_104_ == 0)
{
if (v___x_101_ == 0)
{
lean_object* v___x_105_; 
lean_dec_ref(v_ps_87_);
v___x_105_ = lean_apply_7(v_x_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, lean_box(0));
return v___x_105_;
}
else
{
lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_116_; 
lean_inc(v_included_97_);
lean_inc_ref(v_isCandidateFn_96_);
v_isSharedCheck_116_ = !lean_is_exclusive(v_a_89_);
if (v_isSharedCheck_116_ == 0)
{
lean_object* v_unused_117_; lean_object* v_unused_118_; 
v_unused_117_ = lean_ctor_get(v_a_89_, 1);
lean_dec(v_unused_117_);
v_unused_118_ = lean_ctor_get(v_a_89_, 0);
lean_dec(v_unused_118_);
v___x_107_ = v_a_89_;
v_isShared_108_ = v_isSharedCheck_116_;
goto v_resetjp_106_;
}
else
{
lean_dec(v_a_89_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_116_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
size_t v___x_109_; size_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_109_ = ((size_t)0ULL);
v___x_110_ = lean_usize_of_nat(v___x_99_);
v___x_111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_100_, v___f_103_, v_ps_87_, v___x_109_, v___x_110_, v_included_97_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 1, v___x_111_);
v___x_113_ = v___x_107_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_isCandidateFn_96_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v___x_111_);
v___x_113_ = v_reuseFailAlloc_115_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
lean_object* v___x_114_; 
v___x_114_ = lean_apply_7(v_x_88_, v___x_113_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, lean_box(0));
return v___x_114_;
}
}
}
}
else
{
lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_129_; 
lean_inc(v_included_97_);
lean_inc_ref(v_isCandidateFn_96_);
v_isSharedCheck_129_ = !lean_is_exclusive(v_a_89_);
if (v_isSharedCheck_129_ == 0)
{
lean_object* v_unused_130_; lean_object* v_unused_131_; 
v_unused_130_ = lean_ctor_get(v_a_89_, 1);
lean_dec(v_unused_130_);
v_unused_131_ = lean_ctor_get(v_a_89_, 0);
lean_dec(v_unused_131_);
v___x_120_ = v_a_89_;
v_isShared_121_ = v_isSharedCheck_129_;
goto v_resetjp_119_;
}
else
{
lean_dec(v_a_89_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_129_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
size_t v___x_122_; size_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_122_ = ((size_t)0ULL);
v___x_123_ = lean_usize_of_nat(v___x_99_);
v___x_124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_100_, v___f_103_, v_ps_87_, v___x_122_, v___x_123_, v_included_97_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 1, v___x_124_);
v___x_126_ = v___x_120_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_isCandidateFn_96_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v___x_124_);
v___x_126_ = v_reuseFailAlloc_128_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_127_; 
v___x_127_ = lean_apply_7(v_x_88_, v___x_126_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, lean_box(0));
return v___x_127_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___boxed(lean_object* v_ps_132_, lean_object* v_x_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg(v_ps_132_, v_x_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams(lean_object* v_00_u03b1_142_, lean_object* v_ps_143_, lean_object* v_x_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_isCandidateFn_152_; lean_object* v_included_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v_isCandidateFn_152_ = lean_ctor_get(v_a_145_, 0);
v_included_153_ = lean_ctor_get(v_a_145_, 1);
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = lean_array_get_size(v_ps_143_);
v___x_156_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__9));
v___x_157_ = lean_nat_dec_lt(v___x_154_, v___x_155_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; 
lean_dec_ref(v_ps_143_);
v___x_158_ = lean_apply_7(v_x_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, lean_box(0));
return v___x_158_;
}
else
{
lean_object* v___f_159_; uint8_t v___x_160_; 
v___f_159_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__10));
v___x_160_ = lean_nat_dec_le(v___x_155_, v___x_155_);
if (v___x_160_ == 0)
{
if (v___x_157_ == 0)
{
lean_object* v___x_161_; 
lean_dec_ref(v_ps_143_);
v___x_161_ = lean_apply_7(v_x_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, lean_box(0));
return v___x_161_;
}
else
{
lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_172_; 
lean_inc(v_included_153_);
lean_inc_ref(v_isCandidateFn_152_);
v_isSharedCheck_172_ = !lean_is_exclusive(v_a_145_);
if (v_isSharedCheck_172_ == 0)
{
lean_object* v_unused_173_; lean_object* v_unused_174_; 
v_unused_173_ = lean_ctor_get(v_a_145_, 1);
lean_dec(v_unused_173_);
v_unused_174_ = lean_ctor_get(v_a_145_, 0);
lean_dec(v_unused_174_);
v___x_163_ = v_a_145_;
v_isShared_164_ = v_isSharedCheck_172_;
goto v_resetjp_162_;
}
else
{
lean_dec(v_a_145_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_172_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
size_t v___x_165_; size_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_165_ = ((size_t)0ULL);
v___x_166_ = lean_usize_of_nat(v___x_155_);
v___x_167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_156_, v___f_159_, v_ps_143_, v___x_165_, v___x_166_, v_included_153_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 1, v___x_167_);
v___x_169_ = v___x_163_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_isCandidateFn_152_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_167_);
v___x_169_ = v_reuseFailAlloc_171_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_170_; 
v___x_170_ = lean_apply_7(v_x_144_, v___x_169_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, lean_box(0));
return v___x_170_;
}
}
}
}
else
{
lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_185_; 
lean_inc(v_included_153_);
lean_inc_ref(v_isCandidateFn_152_);
v_isSharedCheck_185_ = !lean_is_exclusive(v_a_145_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; lean_object* v_unused_187_; 
v_unused_186_ = lean_ctor_get(v_a_145_, 1);
lean_dec(v_unused_186_);
v_unused_187_ = lean_ctor_get(v_a_145_, 0);
lean_dec(v_unused_187_);
v___x_176_ = v_a_145_;
v_isShared_177_ = v_isSharedCheck_185_;
goto v_resetjp_175_;
}
else
{
lean_dec(v_a_145_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_185_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
size_t v___x_178_; size_t v___x_179_; lean_object* v___x_180_; lean_object* v___x_182_; 
v___x_178_ = ((size_t)0ULL);
v___x_179_ = lean_usize_of_nat(v___x_155_);
v___x_180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_156_, v___f_159_, v_ps_143_, v___x_178_, v___x_179_, v_included_153_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 1, v___x_180_);
v___x_182_ = v___x_176_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_isCandidateFn_152_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v___x_180_);
v___x_182_ = v_reuseFailAlloc_184_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_183_; 
v___x_183_ = lean_apply_7(v_x_144_, v___x_182_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, lean_box(0));
return v___x_183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withParams___boxed(lean_object* v_00_u03b1_188_, lean_object* v_ps_189_, lean_object* v_x_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_Compiler_LCNF_PullLetDecls_withParams(v_00_u03b1_188_, v_ps_189_, v_x_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withNewScope___redArg(lean_object* v_x_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v_isCandidateFn_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_216_; 
v_isCandidateFn_207_ = lean_ctor_get(v_a_200_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v_a_200_);
if (v_isSharedCheck_216_ == 0)
{
lean_object* v_unused_217_; 
v_unused_217_ = lean_ctor_get(v_a_200_, 1);
lean_dec(v_unused_217_);
v___x_209_ = v_a_200_;
v_isShared_210_ = v_isSharedCheck_216_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_isCandidateFn_207_);
lean_dec(v_a_200_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_216_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = lean_box(1);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 1, v___x_211_);
v___x_213_ = v___x_209_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_isCandidateFn_207_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___x_211_);
v___x_213_ = v_reuseFailAlloc_215_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_214_; 
v___x_214_ = lean_apply_7(v_x_199_, v___x_213_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, lean_box(0));
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withNewScope___redArg___boxed(lean_object* v_x_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Compiler_LCNF_PullLetDecls_withNewScope___redArg(v_x_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withNewScope(lean_object* v_00_u03b1_227_, lean_object* v_x_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_isCandidateFn_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_245_; 
v_isCandidateFn_236_ = lean_ctor_get(v_a_229_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v_a_229_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; 
v_unused_246_ = lean_ctor_get(v_a_229_, 1);
lean_dec(v_unused_246_);
v___x_238_ = v_a_229_;
v_isShared_239_ = v_isSharedCheck_245_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_isCandidateFn_236_);
lean_dec(v_a_229_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_245_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = lean_box(1);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v___x_240_);
v___x_242_ = v___x_238_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_isCandidateFn_236_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v___x_240_);
v___x_242_ = v_reuseFailAlloc_244_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; 
v___x_243_ = lean_apply_7(v_x_228_, v___x_242_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, lean_box(0));
return v___x_243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withNewScope___boxed(lean_object* v_00_u03b1_247_, lean_object* v_x_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Compiler_LCNF_PullLetDecls_withNewScope(v_00_u03b1_247_, v_x_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_PullLetDecls_withCheckpoint_go(lean_object* v_c_257_, lean_object* v_toPull_258_, lean_object* v_i_259_, lean_object* v_included_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_262_ = lean_array_get_size(v_toPull_258_);
v___x_263_ = lean_nat_dec_lt(v_i_259_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; 
lean_dec(v_included_260_);
lean_dec(v_i_259_);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v_c_257_);
lean_ctor_set(v___x_264_, 1, v_a_261_);
return v___x_264_;
}
else
{
lean_object* v_letDecl_265_; uint8_t v___x_266_; uint8_t v___x_267_; 
v_letDecl_265_ = lean_array_fget_borrowed(v_toPull_258_, v_i_259_);
v___x_266_ = 0;
v___x_267_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v___x_266_, v_letDecl_265_, v_included_260_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
lean_inc(v_letDecl_265_);
v___x_268_ = lean_array_push(v_a_261_, v_letDecl_265_);
v___x_269_ = lean_unsigned_to_nat(1u);
v___x_270_ = lean_nat_add(v_i_259_, v___x_269_);
lean_dec(v_i_259_);
v_i_259_ = v___x_270_;
v_a_261_ = v___x_268_;
goto _start;
}
else
{
lean_object* v_fvarId_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v_fst_277_; lean_object* v_snd_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_286_; 
v_fvarId_272_ = lean_ctor_get(v_letDecl_265_, 0);
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = lean_nat_add(v_i_259_, v___x_273_);
lean_dec(v_i_259_);
lean_inc(v_fvarId_272_);
v___x_275_ = l_Lean_FVarIdSet_insert(v_included_260_, v_fvarId_272_);
v___x_276_ = l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_PullLetDecls_withCheckpoint_go(v_c_257_, v_toPull_258_, v___x_274_, v___x_275_, v_a_261_);
v_fst_277_ = lean_ctor_get(v___x_276_, 0);
v_snd_278_ = lean_ctor_get(v___x_276_, 1);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_286_ == 0)
{
v___x_280_ = v___x_276_;
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_snd_278_);
lean_inc(v_fst_277_);
lean_dec(v___x_276_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_284_; 
lean_inc(v_letDecl_265_);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v_letDecl_265_);
lean_ctor_set(v___x_282_, 1, v_fst_277_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_282_);
v___x_284_ = v___x_280_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_snd_278_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_PullLetDecls_withCheckpoint_go___boxed(lean_object* v_c_287_, lean_object* v_toPull_288_, lean_object* v_i_289_, lean_object* v_included_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_PullLetDecls_withCheckpoint_go(v_c_287_, v_toPull_288_, v_i_289_, v_included_290_, v_a_291_);
lean_dec_ref(v_toPull_288_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint(lean_object* v_x_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_303_; lean_object* v_isCandidateFn_304_; lean_object* v_included_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_332_; 
v___x_303_ = lean_st_ref_get(v_a_297_);
v_isCandidateFn_304_ = lean_ctor_get(v_a_296_, 0);
v_included_305_ = lean_ctor_get(v_a_296_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_a_296_);
if (v_isSharedCheck_332_ == 0)
{
v___x_307_ = v_a_296_;
v_isShared_308_ = v_isSharedCheck_332_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_included_305_);
lean_inc(v_isCandidateFn_304_);
lean_dec(v_a_296_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_332_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_309_ = lean_box(1);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___x_309_);
v___x_311_ = v___x_307_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_isCandidateFn_304_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v___x_309_);
v___x_311_ = v_reuseFailAlloc_331_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_312_; 
lean_inc(v_a_297_);
v___x_312_ = lean_apply_7(v_x_295_, v___x_311_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, lean_box(0));
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_330_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_330_ == 0)
{
v___x_315_ = v___x_312_;
v_isShared_316_ = v_isSharedCheck_330_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_312_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_330_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v_fst_321_; lean_object* v_snd_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_317_ = lean_st_ref_get(v_a_297_);
v___x_318_ = lean_array_get_size(v___x_303_);
lean_dec(v___x_303_);
v___x_319_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint___closed__0));
v___x_320_ = l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_PullLetDecls_withCheckpoint_go(v_a_313_, v___x_317_, v___x_318_, v_included_305_, v___x_319_);
lean_dec(v___x_317_);
v_fst_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_fst_321_);
v_snd_322_ = lean_ctor_get(v___x_320_, 1);
lean_inc(v_snd_322_);
lean_dec_ref(v___x_320_);
v___x_323_ = lean_st_ref_take(v_a_297_);
v___x_324_ = l_Array_shrink___redArg(v___x_323_, v___x_318_);
v___x_325_ = l_Array_append___redArg(v___x_324_, v_snd_322_);
lean_dec(v_snd_322_);
v___x_326_ = lean_st_ref_set(v_a_297_, v___x_325_);
lean_dec(v_a_297_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v_fst_321_);
v___x_328_ = v___x_315_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_fst_321_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
else
{
lean_dec(v_included_305_);
lean_dec(v___x_303_);
lean_dec(v_a_297_);
return v___x_312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint___boxed(lean_object* v_x_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint(v_x_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_attachToPull_spec__0(lean_object* v_as_342_, size_t v_i_343_, size_t v_stop_344_, lean_object* v_b_345_){
_start:
{
uint8_t v___x_346_; 
v___x_346_ = lean_usize_dec_eq(v_i_343_, v_stop_344_);
if (v___x_346_ == 0)
{
size_t v___x_347_; size_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_347_ = ((size_t)1ULL);
v___x_348_ = lean_usize_sub(v_i_343_, v___x_347_);
v___x_349_ = lean_array_uget_borrowed(v_as_342_, v___x_348_);
lean_inc(v___x_349_);
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v_b_345_);
v_i_343_ = v___x_348_;
v_b_345_ = v___x_350_;
goto _start;
}
else
{
return v_b_345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_attachToPull_spec__0___boxed(lean_object* v_as_352_, lean_object* v_i_353_, lean_object* v_stop_354_, lean_object* v_b_355_){
_start:
{
size_t v_i_boxed_356_; size_t v_stop_boxed_357_; lean_object* v_res_358_; 
v_i_boxed_356_ = lean_unbox_usize(v_i_353_);
lean_dec(v_i_353_);
v_stop_boxed_357_ = lean_unbox_usize(v_stop_354_);
lean_dec(v_stop_354_);
v_res_358_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_attachToPull_spec__0(v_as_352_, v_i_boxed_356_, v_stop_boxed_357_, v_b_355_);
lean_dec_ref(v_as_352_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_attachToPull___redArg(lean_object* v_c_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_362_ = lean_st_ref_get(v_a_360_);
v___x_363_ = lean_array_get_size(v___x_362_);
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = lean_nat_dec_lt(v___x_364_, v___x_363_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
lean_dec(v___x_362_);
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v_c_359_);
return v___x_366_;
}
else
{
size_t v___x_367_; size_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_367_ = lean_usize_of_nat(v___x_363_);
v___x_368_ = ((size_t)0ULL);
v___x_369_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_attachToPull_spec__0(v___x_362_, v___x_367_, v___x_368_, v_c_359_);
lean_dec(v___x_362_);
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_attachToPull___redArg___boxed(lean_object* v_c_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Compiler_LCNF_PullLetDecls_attachToPull___redArg(v_c_371_, v_a_372_);
lean_dec(v_a_372_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_attachToPull(lean_object* v_c_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_Compiler_LCNF_PullLetDecls_attachToPull___redArg(v_c_375_, v_a_377_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_attachToPull___boxed(lean_object* v_c_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Compiler_LCNF_PullLetDecls_attachToPull(v_c_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_shouldPull(lean_object* v_decl_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_isCandidateFn_405_; lean_object* v_included_406_; uint8_t v___x_407_; uint8_t v___x_408_; 
v_isCandidateFn_405_ = lean_ctor_get(v_a_394_, 0);
lean_inc_ref(v_isCandidateFn_405_);
v_included_406_ = lean_ctor_get(v_a_394_, 1);
lean_inc(v_included_406_);
lean_dec_ref(v_a_394_);
v___x_407_ = 0;
v___x_408_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v___x_407_, v_decl_393_, v_included_406_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; 
lean_inc_ref(v_decl_393_);
v___x_409_ = lean_apply_7(v_isCandidateFn_405_, v_decl_393_, v_included_406_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, lean_box(0));
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_421_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_421_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_421_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_421_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
uint8_t v___x_414_; 
v___x_414_ = lean_unbox(v_a_410_);
if (v___x_414_ == 0)
{
lean_del_object(v___x_412_);
lean_dec(v_a_410_);
lean_dec_ref(v_decl_393_);
goto v___jp_401_;
}
else
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_415_ = lean_st_ref_take(v_a_395_);
v___x_416_ = lean_array_push(v___x_415_, v_decl_393_);
v___x_417_ = lean_st_ref_set(v_a_395_, v___x_416_);
if (v_isShared_413_ == 0)
{
v___x_419_ = v___x_412_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_410_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
else
{
lean_dec_ref(v_decl_393_);
return v___x_409_;
}
}
else
{
lean_dec(v_included_406_);
lean_dec_ref(v_isCandidateFn_405_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec_ref(v_decl_393_);
goto v___jp_401_;
}
v___jp_401_:
{
uint8_t v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_402_ = 0;
v___x_403_ = lean_box(v___x_402_);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_shouldPull___boxed(lean_object* v_decl_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Compiler_LCNF_PullLetDecls_shouldPull(v_decl_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
lean_dec(v_a_424_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(lean_object* v_as_431_, size_t v_i_432_, size_t v_stop_433_, lean_object* v_b_434_){
_start:
{
uint8_t v___x_435_; 
v___x_435_ = lean_usize_dec_eq(v_i_432_, v_stop_433_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v_fvarId_437_; lean_object* v___x_438_; size_t v___x_439_; size_t v___x_440_; 
v___x_436_ = lean_array_uget_borrowed(v_as_431_, v_i_432_);
v_fvarId_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_fvarId_437_);
v___x_438_ = l_Lean_FVarIdSet_insert(v_b_434_, v_fvarId_437_);
v___x_439_ = ((size_t)1ULL);
v___x_440_ = lean_usize_add(v_i_432_, v___x_439_);
v_i_432_ = v___x_440_;
v_b_434_ = v___x_438_;
goto _start;
}
else
{
return v_b_434_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0___boxed(lean_object* v_as_442_, lean_object* v_i_443_, lean_object* v_stop_444_, lean_object* v_b_445_){
_start:
{
size_t v_i_boxed_446_; size_t v_stop_boxed_447_; lean_object* v_res_448_; 
v_i_boxed_446_ = lean_unbox_usize(v_i_443_);
lean_dec(v_i_443_);
v_stop_boxed_447_ = lean_unbox_usize(v_stop_444_);
lean_dec(v_stop_444_);
v_res_448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_as_442_, v_i_boxed_446_, v_stop_boxed_447_, v_b_445_);
lean_dec_ref(v_as_442_);
return v_res_448_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2___closed__0(void){
_start:
{
uint8_t v___x_449_; lean_object* v___x_450_; 
v___x_449_ = 0;
v___x_450_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2(lean_object* v_msg_451_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2___closed__0, &l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2___closed__0);
v___x_453_ = lean_panic_fn(v___x_452_, v_msg_451_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__3(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_457_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__2));
v___x_458_ = lean_unsigned_to_nat(9u);
v___x_459_ = lean_unsigned_to_nat(635u);
v___x_460_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__1));
v___x_461_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__0));
v___x_462_ = l_mkPanicMessageWithDecl(v___x_461_, v___x_460_, v___x_459_, v___x_458_, v___x_457_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0(lean_object* v_code_463_, uint8_t v___x_464_, lean_object* v_decl_465_, lean_object* v_type_466_, lean_object* v_params_467_, lean_object* v_k_468_, lean_object* v_value_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___y_478_; lean_object* v___y_479_; uint8_t v___y_480_; lean_object* v___y_485_; lean_object* v___y_486_; uint8_t v___y_487_; lean_object* v_isCandidateFn_491_; lean_object* v_included_492_; lean_object* v___y_494_; lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v_isCandidateFn_491_ = lean_ctor_get(v___y_470_, 0);
lean_inc_ref(v_isCandidateFn_491_);
v_included_492_ = lean_ctor_get(v___y_470_, 1);
lean_inc(v_included_492_);
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_array_get_size(v_params_467_);
v___x_540_ = lean_nat_dec_lt(v___x_538_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; 
lean_inc(v___y_475_);
lean_inc_ref(v___y_474_);
lean_inc(v___y_473_);
lean_inc_ref(v___y_472_);
lean_inc(v___y_471_);
v___x_541_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_value_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
v___y_494_ = v___x_541_;
goto v___jp_493_;
}
else
{
uint8_t v___x_542_; 
v___x_542_ = lean_nat_dec_le(v___x_539_, v___x_539_);
if (v___x_542_ == 0)
{
if (v___x_540_ == 0)
{
lean_object* v___x_543_; 
lean_inc(v___y_475_);
lean_inc_ref(v___y_474_);
lean_inc(v___y_473_);
lean_inc_ref(v___y_472_);
lean_inc(v___y_471_);
v___x_543_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_value_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
v___y_494_ = v___x_543_;
goto v___jp_493_;
}
else
{
lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_554_; 
v_isSharedCheck_554_ = !lean_is_exclusive(v___y_470_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; lean_object* v_unused_556_; 
v_unused_555_ = lean_ctor_get(v___y_470_, 1);
lean_dec(v_unused_555_);
v_unused_556_ = lean_ctor_get(v___y_470_, 0);
lean_dec(v_unused_556_);
v___x_545_ = v___y_470_;
v_isShared_546_ = v_isSharedCheck_554_;
goto v_resetjp_544_;
}
else
{
lean_dec(v___y_470_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_554_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
size_t v___x_547_; size_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_547_ = ((size_t)0ULL);
v___x_548_ = lean_usize_of_nat(v___x_539_);
lean_inc(v_included_492_);
v___x_549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_467_, v___x_547_, v___x_548_, v_included_492_);
lean_inc_ref(v_isCandidateFn_491_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 1, v___x_549_);
v___x_551_ = v___x_545_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_isCandidateFn_491_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v___x_549_);
v___x_551_ = v_reuseFailAlloc_553_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; 
lean_inc(v___y_475_);
lean_inc_ref(v___y_474_);
lean_inc(v___y_473_);
lean_inc_ref(v___y_472_);
lean_inc(v___y_471_);
v___x_552_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_value_469_, v___x_551_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
v___y_494_ = v___x_552_;
goto v___jp_493_;
}
}
}
}
else
{
lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_567_; 
v_isSharedCheck_567_ = !lean_is_exclusive(v___y_470_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; lean_object* v_unused_569_; 
v_unused_568_ = lean_ctor_get(v___y_470_, 1);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v___y_470_, 0);
lean_dec(v_unused_569_);
v___x_558_ = v___y_470_;
v_isShared_559_ = v_isSharedCheck_567_;
goto v_resetjp_557_;
}
else
{
lean_dec(v___y_470_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_567_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
size_t v___x_560_; size_t v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_560_ = ((size_t)0ULL);
v___x_561_ = lean_usize_of_nat(v___x_539_);
lean_inc(v_included_492_);
v___x_562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_467_, v___x_560_, v___x_561_, v_included_492_);
lean_inc_ref(v_isCandidateFn_491_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 1, v___x_562_);
v___x_564_ = v___x_558_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_isCandidateFn_491_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_562_);
v___x_564_ = v_reuseFailAlloc_566_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_565_; 
lean_inc(v___y_475_);
lean_inc_ref(v___y_474_);
lean_inc(v___y_473_);
lean_inc_ref(v___y_472_);
lean_inc(v___y_471_);
v___x_565_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_value_469_, v___x_564_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
v___y_494_ = v___x_565_;
goto v___jp_493_;
}
}
}
}
v___jp_477_:
{
if (v___y_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; 
lean_dec_ref(v_code_463_);
v___x_481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_481_, 0, v___y_478_);
lean_ctor_set(v___x_481_, 1, v___y_479_);
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
return v___x_482_;
}
else
{
lean_object* v___x_483_; 
lean_dec_ref(v___y_479_);
lean_dec_ref(v___y_478_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v_code_463_);
return v___x_483_;
}
}
v___jp_484_:
{
if (v___y_487_ == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec_ref(v_code_463_);
v___x_488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_488_, 0, v___y_485_);
lean_ctor_set(v___x_488_, 1, v___y_486_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
else
{
lean_object* v___x_490_; 
lean_dec_ref(v___y_486_);
lean_dec_ref(v___y_485_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v_code_463_);
return v___x_490_;
}
}
v___jp_493_:
{
if (lean_obj_tag(v___y_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_496_; 
v_a_495_ = lean_ctor_get(v___y_494_, 0);
lean_inc(v_a_495_);
lean_dec_ref(v___y_494_);
v___x_496_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_464_, v_decl_465_, v_type_466_, v_params_467_, v_a_495_, v___y_473_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v_fvarId_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref(v___x_496_);
v_fvarId_498_ = lean_ctor_get(v_a_497_, 0);
lean_inc(v_fvarId_498_);
v___x_499_ = l_Lean_FVarIdSet_insert(v_included_492_, v_fvarId_498_);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v_isCandidateFn_491_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_k_468_, v___x_500_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
if (lean_obj_tag(v___x_501_) == 0)
{
switch(lean_obj_tag(v_code_463_))
{
case 1:
{
lean_object* v_a_502_; lean_object* v_decl_503_; lean_object* v_k_504_; size_t v___x_505_; size_t v___x_506_; uint8_t v___x_507_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref(v___x_501_);
v_decl_503_ = lean_ctor_get(v_code_463_, 0);
v_k_504_ = lean_ctor_get(v_code_463_, 1);
v___x_505_ = lean_ptr_addr(v_k_504_);
v___x_506_ = lean_ptr_addr(v_a_502_);
v___x_507_ = lean_usize_dec_eq(v___x_505_, v___x_506_);
if (v___x_507_ == 0)
{
v___y_478_ = v_a_497_;
v___y_479_ = v_a_502_;
v___y_480_ = v___x_507_;
goto v___jp_477_;
}
else
{
size_t v___x_508_; size_t v___x_509_; uint8_t v___x_510_; 
v___x_508_ = lean_ptr_addr(v_decl_503_);
v___x_509_ = lean_ptr_addr(v_a_497_);
v___x_510_ = lean_usize_dec_eq(v___x_508_, v___x_509_);
v___y_478_ = v_a_497_;
v___y_479_ = v_a_502_;
v___y_480_ = v___x_510_;
goto v___jp_477_;
}
}
case 2:
{
lean_object* v_a_511_; lean_object* v_decl_512_; lean_object* v_k_513_; size_t v___x_514_; size_t v___x_515_; uint8_t v___x_516_; 
v_a_511_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_511_);
lean_dec_ref(v___x_501_);
v_decl_512_ = lean_ctor_get(v_code_463_, 0);
v_k_513_ = lean_ctor_get(v_code_463_, 1);
v___x_514_ = lean_ptr_addr(v_k_513_);
v___x_515_ = lean_ptr_addr(v_a_511_);
v___x_516_ = lean_usize_dec_eq(v___x_514_, v___x_515_);
if (v___x_516_ == 0)
{
v___y_485_ = v_a_497_;
v___y_486_ = v_a_511_;
v___y_487_ = v___x_516_;
goto v___jp_484_;
}
else
{
size_t v___x_517_; size_t v___x_518_; uint8_t v___x_519_; 
v___x_517_ = lean_ptr_addr(v_decl_512_);
v___x_518_ = lean_ptr_addr(v_a_497_);
v___x_519_ = lean_usize_dec_eq(v___x_517_, v___x_518_);
v___y_485_ = v_a_497_;
v___y_486_ = v_a_511_;
v___y_487_ = v___x_519_;
goto v___jp_484_;
}
}
default: 
{
lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_528_; 
lean_dec(v_a_497_);
lean_dec_ref(v_code_463_);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; 
v_unused_529_ = lean_ctor_get(v___x_501_, 0);
lean_dec(v_unused_529_);
v___x_521_ = v___x_501_;
v_isShared_522_ = v_isSharedCheck_528_;
goto v_resetjp_520_;
}
else
{
lean_dec(v___x_501_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_528_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_523_ = lean_obj_once(&l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__3, &l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__3_once, _init_l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__3);
v___x_524_ = l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2(v___x_523_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_524_);
v___x_526_ = v___x_521_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
else
{
lean_dec(v_a_497_);
lean_dec_ref(v_code_463_);
return v___x_501_;
}
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
lean_dec(v_included_492_);
lean_dec_ref(v_isCandidateFn_491_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v_k_468_);
lean_dec_ref(v_code_463_);
v_a_530_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_496_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_496_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
else
{
lean_dec(v_included_492_);
lean_dec_ref(v_isCandidateFn_491_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v_k_468_);
lean_dec_ref(v_params_467_);
lean_dec_ref(v_type_466_);
lean_dec_ref(v_decl_465_);
lean_dec_ref(v_code_463_);
return v___y_494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___boxed(lean_object* v_code_570_, lean_object* v___x_571_, lean_object* v_decl_572_, lean_object* v_type_573_, lean_object* v_params_574_, lean_object* v_k_575_, lean_object* v_value_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
uint8_t v___x_4908__boxed_584_; lean_object* v_res_585_; 
v___x_4908__boxed_584_ = lean_unbox(v___x_571_);
v_res_585_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0(v_code_570_, v___x_4908__boxed_584_, v_decl_572_, v_type_573_, v_params_574_, v_k_575_, v_value_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__1___boxed(lean_object* v___x_589_, lean_object* v_alts_590_, lean_object* v_typeName_591_, lean_object* v_resultType_592_, lean_object* v_discr_593_, lean_object* v_code_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__1(v___x_589_, v_alts_590_, v_typeName_591_, v_resultType_592_, v_discr_593_, v_code_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(lean_object* v_code_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_decl_612_; lean_object* v_k_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; 
switch(lean_obj_tag(v_code_603_))
{
case 4:
{
lean_object* v_cases_627_; lean_object* v_typeName_628_; lean_object* v_resultType_629_; lean_object* v_discr_630_; lean_object* v_alts_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v_cases_627_ = lean_ctor_get(v_code_603_, 0);
v_typeName_628_ = lean_ctor_get(v_cases_627_, 0);
v_resultType_629_ = lean_ctor_get(v_cases_627_, 1);
v_discr_630_ = lean_ctor_get(v_cases_627_, 2);
v_alts_631_ = lean_ctor_get(v_cases_627_, 3);
v___x_632_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___closed__1));
v___x_633_ = lean_name_eq(v_typeName_628_, v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___f_635_; lean_object* v___x_636_; 
lean_inc_ref(v_alts_631_);
lean_inc(v_discr_630_);
lean_inc_ref(v_resultType_629_);
lean_inc(v_typeName_628_);
v___x_634_ = lean_unsigned_to_nat(0u);
v___f_635_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__1___boxed), 13, 6);
lean_closure_set(v___f_635_, 0, v___x_634_);
lean_closure_set(v___f_635_, 1, v_alts_631_);
lean_closure_set(v___f_635_, 2, v_typeName_628_);
lean_closure_set(v___f_635_, 3, v_resultType_629_);
lean_closure_set(v___f_635_, 4, v_discr_630_);
lean_closure_set(v___f_635_, 5, v_code_603_);
v___x_636_ = l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint(v___f_635_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
return v___x_636_;
}
else
{
lean_object* v___x_637_; 
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v_code_603_);
return v___x_637_;
}
}
case 0:
{
lean_object* v_decl_638_; lean_object* v_k_639_; lean_object* v___x_640_; 
v_decl_638_ = lean_ctor_get(v_code_603_, 0);
v_k_639_ = lean_ctor_get(v_code_603_, 1);
lean_inc(v_a_609_);
lean_inc_ref(v_a_608_);
lean_inc(v_a_607_);
lean_inc_ref(v_a_606_);
lean_inc_ref(v_a_604_);
lean_inc_ref(v_decl_638_);
v___x_640_ = l_Lean_Compiler_LCNF_PullLetDecls_shouldPull(v_decl_638_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; uint8_t v___x_642_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
lean_dec_ref(v___x_640_);
v___x_642_ = lean_unbox(v_a_641_);
lean_dec(v_a_641_);
if (v___x_642_ == 0)
{
lean_object* v_fvarId_643_; lean_object* v_isCandidateFn_644_; lean_object* v_included_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_677_; 
v_fvarId_643_ = lean_ctor_get(v_decl_638_, 0);
v_isCandidateFn_644_ = lean_ctor_get(v_a_604_, 0);
v_included_645_ = lean_ctor_get(v_a_604_, 1);
v_isSharedCheck_677_ = !lean_is_exclusive(v_a_604_);
if (v_isSharedCheck_677_ == 0)
{
v___x_647_ = v_a_604_;
v_isShared_648_ = v_isSharedCheck_677_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_included_645_);
lean_inc(v_isCandidateFn_644_);
lean_dec(v_a_604_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_677_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v___x_651_; 
lean_inc(v_fvarId_643_);
v___x_649_ = l_Lean_FVarIdSet_insert(v_included_645_, v_fvarId_643_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v___x_649_);
v___x_651_ = v___x_647_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_isCandidateFn_644_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v___x_649_);
v___x_651_ = v_reuseFailAlloc_676_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_652_; 
lean_inc_ref(v_k_639_);
v___x_652_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_k_639_, v___x_651_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_675_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_675_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_675_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_675_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
size_t v___x_657_; size_t v___x_658_; uint8_t v___x_659_; 
v___x_657_ = lean_ptr_addr(v_k_639_);
v___x_658_ = lean_ptr_addr(v_a_653_);
v___x_659_ = lean_usize_dec_eq(v___x_657_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_669_; 
lean_inc_ref(v_decl_638_);
v_isSharedCheck_669_ = !lean_is_exclusive(v_code_603_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; lean_object* v_unused_671_; 
v_unused_670_ = lean_ctor_get(v_code_603_, 1);
lean_dec(v_unused_670_);
v_unused_671_ = lean_ctor_get(v_code_603_, 0);
lean_dec(v_unused_671_);
v___x_661_ = v_code_603_;
v_isShared_662_ = v_isSharedCheck_669_;
goto v_resetjp_660_;
}
else
{
lean_dec(v_code_603_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_669_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v_a_653_);
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_decl_638_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_a_653_);
v___x_664_ = v_reuseFailAlloc_668_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_666_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_664_);
v___x_666_ = v___x_655_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
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
else
{
lean_object* v___x_673_; 
lean_dec(v_a_653_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v_code_603_);
v___x_673_ = v___x_655_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_code_603_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
else
{
lean_dec_ref(v_code_603_);
return v___x_652_;
}
}
}
}
else
{
lean_inc_ref(v_k_639_);
lean_dec_ref(v_code_603_);
v_code_603_ = v_k_639_;
goto _start;
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v_code_603_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
v_a_679_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_640_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_640_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
case 1:
{
lean_object* v_decl_687_; lean_object* v_k_688_; 
v_decl_687_ = lean_ctor_get(v_code_603_, 0);
v_k_688_ = lean_ctor_get(v_code_603_, 1);
lean_inc_ref(v_k_688_);
lean_inc_ref(v_decl_687_);
v_decl_612_ = v_decl_687_;
v_k_613_ = v_k_688_;
v___y_614_ = v_a_604_;
v___y_615_ = v_a_605_;
v___y_616_ = v_a_606_;
v___y_617_ = v_a_607_;
v___y_618_ = v_a_608_;
v___y_619_ = v_a_609_;
goto v___jp_611_;
}
case 2:
{
lean_object* v_decl_689_; lean_object* v_k_690_; 
v_decl_689_ = lean_ctor_get(v_code_603_, 0);
v_k_690_ = lean_ctor_get(v_code_603_, 1);
lean_inc_ref(v_k_690_);
lean_inc_ref(v_decl_689_);
v_decl_612_ = v_decl_689_;
v_k_613_ = v_k_690_;
v___y_614_ = v_a_604_;
v___y_615_ = v_a_605_;
v___y_616_ = v_a_606_;
v___y_617_ = v_a_607_;
v___y_618_ = v_a_608_;
v___y_619_ = v_a_609_;
goto v___jp_611_;
}
default: 
{
lean_object* v___x_691_; 
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v_code_603_);
return v___x_691_;
}
}
v___jp_611_:
{
lean_object* v_params_620_; lean_object* v_type_621_; lean_object* v_value_622_; uint8_t v___x_623_; lean_object* v___x_624_; lean_object* v___f_625_; lean_object* v___x_626_; 
v_params_620_ = lean_ctor_get(v_decl_612_, 2);
lean_inc_ref(v_params_620_);
v_type_621_ = lean_ctor_get(v_decl_612_, 3);
lean_inc_ref(v_type_621_);
v_value_622_ = lean_ctor_get(v_decl_612_, 4);
lean_inc_ref(v_value_622_);
v___x_623_ = 0;
v___x_624_ = lean_box(v___x_623_);
v___f_625_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___boxed), 14, 7);
lean_closure_set(v___f_625_, 0, v_code_603_);
lean_closure_set(v___f_625_, 1, v___x_624_);
lean_closure_set(v___f_625_, 2, v_decl_612_);
lean_closure_set(v___f_625_, 3, v_type_621_);
lean_closure_set(v___f_625_, 4, v_params_620_);
lean_closure_set(v___f_625_, 5, v_k_613_);
lean_closure_set(v___f_625_, 6, v_value_622_);
v___x_626_ = l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint(v___f_625_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
return v___x_626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullAlt(lean_object* v_alt_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v___y_701_; 
if (lean_obj_tag(v_alt_692_) == 0)
{
lean_object* v_params_719_; lean_object* v_code_720_; lean_object* v_isCandidateFn_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_752_; 
v_params_719_ = lean_ctor_get(v_alt_692_, 1);
v_code_720_ = lean_ctor_get(v_alt_692_, 2);
v_isCandidateFn_721_ = lean_ctor_get(v_a_693_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v_a_693_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; 
v_unused_753_ = lean_ctor_get(v_a_693_, 1);
lean_dec(v_unused_753_);
v___x_723_ = v_a_693_;
v_isShared_724_ = v_isSharedCheck_752_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_isCandidateFn_721_);
lean_dec(v_a_693_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_752_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_725_ = lean_box(1);
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = lean_array_get_size(v_params_719_);
v___x_728_ = lean_nat_dec_lt(v___x_726_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_730_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v___x_725_);
v___x_730_ = v___x_723_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_isCandidateFn_721_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_725_);
v___x_730_ = v_reuseFailAlloc_732_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_731_; 
lean_inc_ref(v_code_720_);
v___x_731_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_code_720_, v___x_730_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
v___y_701_ = v___x_731_;
goto v___jp_700_;
}
}
else
{
uint8_t v___x_733_; 
v___x_733_ = lean_nat_dec_le(v___x_727_, v___x_727_);
if (v___x_733_ == 0)
{
if (v___x_728_ == 0)
{
lean_object* v___x_735_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v___x_725_);
v___x_735_ = v___x_723_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_isCandidateFn_721_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v___x_725_);
v___x_735_ = v_reuseFailAlloc_737_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_736_; 
lean_inc_ref(v_code_720_);
v___x_736_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_code_720_, v___x_735_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
v___y_701_ = v___x_736_;
goto v___jp_700_;
}
}
else
{
size_t v___x_738_; size_t v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_738_ = ((size_t)0ULL);
v___x_739_ = lean_usize_of_nat(v___x_727_);
v___x_740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_719_, v___x_738_, v___x_739_, v___x_725_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v___x_740_);
v___x_742_ = v___x_723_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_isCandidateFn_721_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v___x_740_);
v___x_742_ = v_reuseFailAlloc_744_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; 
lean_inc_ref(v_code_720_);
v___x_743_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_code_720_, v___x_742_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
v___y_701_ = v___x_743_;
goto v___jp_700_;
}
}
}
else
{
size_t v___x_745_; size_t v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_745_ = ((size_t)0ULL);
v___x_746_ = lean_usize_of_nat(v___x_727_);
v___x_747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_719_, v___x_745_, v___x_746_, v___x_725_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v___x_747_);
v___x_749_ = v___x_723_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_isCandidateFn_721_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v___x_747_);
v___x_749_ = v_reuseFailAlloc_751_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; 
lean_inc_ref(v_code_720_);
v___x_750_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_code_720_, v___x_749_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
v___y_701_ = v___x_750_;
goto v___jp_700_;
}
}
}
}
}
else
{
lean_object* v_code_754_; lean_object* v_isCandidateFn_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_781_; 
v_code_754_ = lean_ctor_get(v_alt_692_, 0);
v_isCandidateFn_755_ = lean_ctor_get(v_a_693_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v_a_693_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; 
v_unused_782_ = lean_ctor_get(v_a_693_, 1);
lean_dec(v_unused_782_);
v___x_757_ = v_a_693_;
v_isShared_758_ = v_isSharedCheck_781_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_isCandidateFn_755_);
lean_dec(v_a_693_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_781_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_759_ = lean_box(1);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 1, v___x_759_);
v___x_761_ = v___x_757_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_isCandidateFn_755_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_780_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_762_; 
lean_inc_ref(v_code_754_);
v___x_762_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_code_754_, v___x_761_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_771_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_771_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_771_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_771_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_767_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_692_, v_a_763_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_767_);
v___x_769_ = v___x_765_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec_ref(v_alt_692_);
v_a_772_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_762_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_762_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
}
v___jp_700_:
{
if (lean_obj_tag(v___y_701_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_710_; 
v_a_702_ = lean_ctor_get(v___y_701_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___y_701_);
if (v_isSharedCheck_710_ == 0)
{
v___x_704_ = v___y_701_;
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___y_701_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_706_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_692_, v_a_702_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_706_);
v___x_708_ = v___x_704_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec_ref(v_alt_692_);
v_a_711_ = lean_ctor_get(v___y_701_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___y_701_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___y_701_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___y_701_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__3(lean_object* v_i_783_, lean_object* v_as_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = lean_array_get_size(v_as_784_);
v___x_793_ = lean_nat_dec_lt(v_i_783_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; 
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v_i_783_);
v___x_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_794_, 0, v_as_784_);
return v___x_794_;
}
else
{
lean_object* v_a_795_; lean_object* v___x_796_; 
v_a_795_ = lean_array_fget_borrowed(v_as_784_, v_i_783_);
lean_inc(v___y_790_);
lean_inc_ref(v___y_789_);
lean_inc(v___y_788_);
lean_inc_ref(v___y_787_);
lean_inc(v___y_786_);
lean_inc_ref(v___y_785_);
lean_inc(v_a_795_);
v___x_796_ = l_Lean_Compiler_LCNF_PullLetDecls_pullAlt(v_a_795_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; size_t v___x_798_; size_t v___x_799_; uint8_t v___x_800_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref(v___x_796_);
v___x_798_ = lean_ptr_addr(v_a_795_);
v___x_799_ = lean_ptr_addr(v_a_797_);
v___x_800_ = lean_usize_dec_eq(v___x_798_, v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = lean_unsigned_to_nat(1u);
v___x_802_ = lean_nat_add(v_i_783_, v___x_801_);
v___x_803_ = lean_array_fset(v_as_784_, v_i_783_, v_a_797_);
lean_dec(v_i_783_);
v_i_783_ = v___x_802_;
v_as_784_ = v___x_803_;
goto _start;
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec(v_a_797_);
v___x_805_ = lean_unsigned_to_nat(1u);
v___x_806_ = lean_nat_add(v_i_783_, v___x_805_);
lean_dec(v_i_783_);
v_i_783_ = v___x_806_;
goto _start;
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec_ref(v_as_784_);
lean_dec(v_i_783_);
v_a_808_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_796_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_796_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__1(lean_object* v___x_816_, lean_object* v_alts_817_, lean_object* v_typeName_818_, lean_object* v_resultType_819_, lean_object* v_discr_820_, lean_object* v_code_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v___x_829_; 
lean_inc_ref(v_alts_817_);
v___x_829_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__3(v___x_816_, v_alts_817_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_845_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_845_ == 0)
{
v___x_832_ = v___x_829_;
v_isShared_833_ = v_isSharedCheck_845_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_829_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_845_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
size_t v___x_834_; size_t v___x_835_; uint8_t v___x_836_; 
v___x_834_ = lean_ptr_addr(v_alts_817_);
lean_dec_ref(v_alts_817_);
v___x_835_ = lean_ptr_addr(v_a_830_);
v___x_836_ = lean_usize_dec_eq(v___x_834_, v___x_835_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
lean_dec_ref(v_code_821_);
v___x_837_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_837_, 0, v_typeName_818_);
lean_ctor_set(v___x_837_, 1, v_resultType_819_);
lean_ctor_set(v___x_837_, 2, v_discr_820_);
lean_ctor_set(v___x_837_, 3, v_a_830_);
v___x_838_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v___x_838_);
v___x_840_ = v___x_832_;
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
else
{
lean_object* v___x_843_; 
lean_dec(v_a_830_);
lean_dec(v_discr_820_);
lean_dec_ref(v_resultType_819_);
lean_dec(v_typeName_818_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v_code_821_);
v___x_843_ = v___x_832_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_code_821_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec_ref(v_code_821_);
lean_dec(v_discr_820_);
lean_dec_ref(v_resultType_819_);
lean_dec(v_typeName_818_);
lean_dec_ref(v_alts_817_);
v_a_846_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_829_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_829_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__3___boxed(lean_object* v_i_854_, lean_object* v_as_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__3(v_i_854_, v_as_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___boxed(lean_object* v_code_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(v_code_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_pullAlt___boxed(lean_object* v_alt_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_Compiler_LCNF_PullLetDecls_pullAlt(v_alt_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg(lean_object* v_x_882_, lean_object* v_isCandidateFn_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_889_ = ((lean_object*)(l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint___closed__0));
v___x_890_ = lean_st_mk_ref(v___x_889_);
v___x_891_ = lean_box(1);
v___x_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_892_, 0, v_isCandidateFn_883_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
lean_inc(v___x_890_);
v___x_893_ = lean_apply_7(v_x_882_, v___x_892_, v___x_890_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, lean_box(0));
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_902_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_902_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_902_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_902_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_898_ = lean_st_ref_get(v___x_890_);
lean_dec(v___x_890_);
lean_dec(v___x_898_);
if (v_isShared_897_ == 0)
{
v___x_900_ = v___x_896_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_894_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
else
{
lean_dec(v___x_890_);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg___boxed(lean_object* v_x_903_, lean_object* v_isCandidateFn_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg(v_x_903_, v_isCandidateFn_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_PullM_run(lean_object* v_00_u03b1_911_, lean_object* v_x_912_, lean_object* v_isCandidateFn_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg(v_x_912_, v_isCandidateFn_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___boxed(lean_object* v_00_u03b1_920_, lean_object* v_x_921_, lean_object* v_isCandidateFn_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_Compiler_LCNF_PullLetDecls_PullM_run(v_00_u03b1_920_, v_x_921_, v_isCandidateFn_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(lean_object* v_f_929_, lean_object* v_v_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
if (lean_obj_tag(v_v_930_) == 0)
{
lean_object* v_code_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_962_; 
v_code_938_ = lean_ctor_get(v_v_930_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v_v_930_);
if (v_isSharedCheck_962_ == 0)
{
v___x_940_ = v_v_930_;
v_isShared_941_ = v_isSharedCheck_962_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_code_938_);
lean_dec(v_v_930_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_962_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; 
v___x_942_ = lean_apply_8(v_f_929_, v_code_938_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, lean_box(0));
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_953_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_953_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_953_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_953_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v_a_943_);
v___x_948_ = v___x_940_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_952_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_950_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_948_);
v___x_950_ = v___x_945_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_948_);
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
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_del_object(v___x_940_);
v_a_954_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_942_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_942_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
else
{
lean_object* v___x_963_; 
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec_ref(v_f_929_);
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v_v_930_);
return v___x_963_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg___boxed(lean_object* v_f_964_, lean_object* v_v_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(v_f_964_, v_v_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0(uint8_t v_pu_974_, lean_object* v_f_975_, lean_object* v_v_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(v_f_975_, v_v_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___boxed(lean_object* v_pu_985_, lean_object* v_f_986_, lean_object* v_v_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
uint8_t v_pu_boxed_995_; lean_object* v_res_996_; 
v_pu_boxed_995_ = lean_unbox(v_pu_985_);
v_res_996_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0(v_pu_boxed_995_, v_f_986_, v_v_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0(lean_object* v___x_998_, lean_object* v_value_999_, lean_object* v_toSignature_1000_, uint8_t v_recursive_1001_, lean_object* v_inlineAttr_x3f_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___x_1010_; 
lean_inc(v___y_1008_);
lean_inc_ref(v___y_1007_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1004_);
lean_inc_ref(v___y_1003_);
v___x_1010_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(v___x_998_, v_value_999_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref(v___x_1010_);
v___x_1012_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0___closed__0));
v___x_1013_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(v___x_1012_, v_a_1011_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1022_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1018_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1018_, 0, v_toSignature_1000_);
lean_ctor_set(v___x_1018_, 1, v_a_1014_);
lean_ctor_set(v___x_1018_, 2, v_inlineAttr_x3f_1002_);
lean_ctor_set_uint8(v___x_1018_, sizeof(void*)*3, v_recursive_1001_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1018_);
v___x_1020_ = v___x_1016_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v_inlineAttr_x3f_1002_);
lean_dec_ref(v_toSignature_1000_);
v_a_1023_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1013_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1013_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v_inlineAttr_x3f_1002_);
lean_dec_ref(v_toSignature_1000_);
v_a_1031_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1010_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1010_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0___boxed(lean_object* v___x_1039_, lean_object* v_value_1040_, lean_object* v_toSignature_1041_, lean_object* v_recursive_1042_, lean_object* v_inlineAttr_x3f_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
uint8_t v_recursive_boxed_1051_; lean_object* v_res_1052_; 
v_recursive_boxed_1051_ = lean_unbox(v_recursive_1042_);
v_res_1052_ = l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0(v___x_1039_, v_value_1040_, v_toSignature_1041_, v_recursive_boxed_1051_, v_inlineAttr_x3f_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__1(lean_object* v_params_1053_, lean_object* v___f_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v_isCandidateFn_1062_; lean_object* v_included_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v_isCandidateFn_1062_ = lean_ctor_get(v___y_1055_, 0);
v_included_1063_ = lean_ctor_get(v___y_1055_, 1);
v___x_1064_ = lean_unsigned_to_nat(0u);
v___x_1065_ = lean_array_get_size(v_params_1053_);
v___x_1066_ = lean_nat_dec_lt(v___x_1064_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_apply_7(v___f_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, lean_box(0));
return v___x_1067_;
}
else
{
uint8_t v___x_1068_; 
v___x_1068_ = lean_nat_dec_le(v___x_1065_, v___x_1065_);
if (v___x_1068_ == 0)
{
if (v___x_1066_ == 0)
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_apply_7(v___f_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, lean_box(0));
return v___x_1069_;
}
else
{
lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1080_; 
lean_inc(v_included_1063_);
lean_inc_ref(v_isCandidateFn_1062_);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___y_1055_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; lean_object* v_unused_1082_; 
v_unused_1081_ = lean_ctor_get(v___y_1055_, 1);
lean_dec(v_unused_1081_);
v_unused_1082_ = lean_ctor_get(v___y_1055_, 0);
lean_dec(v_unused_1082_);
v___x_1071_ = v___y_1055_;
v_isShared_1072_ = v_isSharedCheck_1080_;
goto v_resetjp_1070_;
}
else
{
lean_dec(v___y_1055_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1080_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
size_t v___x_1073_; size_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1073_ = ((size_t)0ULL);
v___x_1074_ = lean_usize_of_nat(v___x_1065_);
v___x_1075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_1053_, v___x_1073_, v___x_1074_, v_included_1063_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v___x_1075_);
v___x_1077_ = v___x_1071_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_isCandidateFn_1062_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_apply_7(v___f_1054_, v___x_1077_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, lean_box(0));
return v___x_1078_;
}
}
}
}
else
{
lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1093_; 
lean_inc(v_included_1063_);
lean_inc_ref(v_isCandidateFn_1062_);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___y_1055_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; lean_object* v_unused_1095_; 
v_unused_1094_ = lean_ctor_get(v___y_1055_, 1);
lean_dec(v_unused_1094_);
v_unused_1095_ = lean_ctor_get(v___y_1055_, 0);
lean_dec(v_unused_1095_);
v___x_1084_ = v___y_1055_;
v_isShared_1085_ = v_isSharedCheck_1093_;
goto v_resetjp_1083_;
}
else
{
lean_dec(v___y_1055_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1093_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
size_t v___x_1086_; size_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1086_ = ((size_t)0ULL);
v___x_1087_ = lean_usize_of_nat(v___x_1065_);
v___x_1088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_1053_, v___x_1086_, v___x_1087_, v_included_1063_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 1, v___x_1088_);
v___x_1090_ = v___x_1084_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_isCandidateFn_1062_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_apply_7(v___f_1054_, v___x_1090_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, lean_box(0));
return v___x_1091_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__1___boxed(lean_object* v_params_1096_, lean_object* v___f_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__1(v_params_1096_, v___f_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec_ref(v_params_1096_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls(lean_object* v_decl_1107_, lean_object* v_isCandidateFn_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v_toSignature_1114_; lean_object* v_value_1115_; uint8_t v_recursive_1116_; lean_object* v_inlineAttr_x3f_1117_; lean_object* v_params_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___f_1121_; lean_object* v___f_1122_; lean_object* v___x_1123_; 
v_toSignature_1114_ = lean_ctor_get(v_decl_1107_, 0);
lean_inc_ref(v_toSignature_1114_);
v_value_1115_ = lean_ctor_get(v_decl_1107_, 1);
lean_inc_ref(v_value_1115_);
v_recursive_1116_ = lean_ctor_get_uint8(v_decl_1107_, sizeof(void*)*3);
v_inlineAttr_x3f_1117_ = lean_ctor_get(v_decl_1107_, 2);
lean_inc(v_inlineAttr_x3f_1117_);
lean_dec_ref(v_decl_1107_);
v_params_1118_ = lean_ctor_get(v_toSignature_1114_, 3);
lean_inc_ref(v_params_1118_);
v___x_1119_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_pullLetDecls___closed__0));
v___x_1120_ = lean_box(v_recursive_1116_);
v___f_1121_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1121_, 0, v___x_1119_);
lean_closure_set(v___f_1121_, 1, v_value_1115_);
lean_closure_set(v___f_1121_, 2, v_toSignature_1114_);
lean_closure_set(v___f_1121_, 3, v___x_1120_);
lean_closure_set(v___f_1121_, 4, v_inlineAttr_x3f_1117_);
v___f_1122_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__1___boxed), 9, 2);
lean_closure_set(v___f_1122_, 0, v_params_1118_);
lean_closure_set(v___f_1122_, 1, v___f_1121_);
v___x_1123_ = l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg(v___f_1122_, v_isCandidateFn_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullLetDecls___boxed(lean_object* v_decl_1124_, lean_object* v_isCandidateFn_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_Compiler_LCNF_Decl_pullLetDecls(v_decl_1124_, v_isCandidateFn_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
return v_res_1131_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg(lean_object* v_k_1132_, lean_object* v_t_1133_){
_start:
{
if (lean_obj_tag(v_t_1133_) == 0)
{
lean_object* v_k_1134_; lean_object* v_l_1135_; lean_object* v_r_1136_; uint8_t v___x_1137_; 
v_k_1134_ = lean_ctor_get(v_t_1133_, 1);
v_l_1135_ = lean_ctor_get(v_t_1133_, 3);
v_r_1136_ = lean_ctor_get(v_t_1133_, 4);
v___x_1137_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1132_, v_k_1134_);
switch(v___x_1137_)
{
case 0:
{
v_t_1133_ = v_l_1135_;
goto _start;
}
case 1:
{
uint8_t v___x_1139_; 
v___x_1139_ = 1;
return v___x_1139_;
}
default: 
{
v_t_1133_ = v_r_1136_;
goto _start;
}
}
}
else
{
uint8_t v___x_1141_; 
v___x_1141_ = 0;
return v___x_1141_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg___boxed(lean_object* v_k_1142_, lean_object* v_t_1143_){
_start:
{
uint8_t v_res_1144_; lean_object* v_r_1145_; 
v_res_1144_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg(v_k_1142_, v_t_1143_);
lean_dec(v_t_1143_);
lean_dec(v_k_1142_);
v_r_1145_ = lean_box(v_res_1144_);
return v_r_1145_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1(lean_object* v_as_1146_, size_t v_i_1147_, size_t v_stop_1148_){
_start:
{
uint8_t v___x_1149_; 
v___x_1149_ = lean_usize_dec_eq(v_i_1147_, v_stop_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1150_ = lean_array_uget_borrowed(v_as_1146_, v_i_1147_);
v___x_1151_ = lean_box(0);
v___x_1152_ = l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(v___x_1150_, v___x_1151_);
if (v___x_1152_ == 0)
{
size_t v___x_1153_; size_t v___x_1154_; 
v___x_1153_ = ((size_t)1ULL);
v___x_1154_ = lean_usize_add(v_i_1147_, v___x_1153_);
v_i_1147_ = v___x_1154_;
goto _start;
}
else
{
return v___x_1152_;
}
}
else
{
uint8_t v___x_1156_; 
v___x_1156_ = 0;
return v___x_1156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1___boxed(lean_object* v_as_1157_, lean_object* v_i_1158_, lean_object* v_stop_1159_){
_start:
{
size_t v_i_boxed_1160_; size_t v_stop_boxed_1161_; uint8_t v_res_1162_; lean_object* v_r_1163_; 
v_i_boxed_1160_ = lean_unbox_usize(v_i_1158_);
lean_dec(v_i_1158_);
v_stop_boxed_1161_ = lean_unbox_usize(v_stop_1159_);
lean_dec(v_stop_1159_);
v_res_1162_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1(v_as_1157_, v_i_boxed_1160_, v_stop_boxed_1161_);
lean_dec_ref(v_as_1157_);
v_r_1163_ = lean_box(v_res_1162_);
return v_r_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullInstances___lam__0(lean_object* v_letDecl_1164_, lean_object* v_candidates_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_type_1171_; lean_object* v_value_1172_; lean_object* v___y_1174_; lean_object* v___y_1206_; 
v_type_1171_ = lean_ctor_get(v_letDecl_1164_, 2);
v_value_1172_ = lean_ctor_get(v_letDecl_1164_, 3);
if (lean_obj_tag(v_value_1172_) == 3)
{
lean_object* v_args_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v_args_1217_ = lean_ctor_get(v_value_1172_, 2);
v___x_1218_ = lean_unsigned_to_nat(0u);
v___x_1219_ = lean_array_get_size(v_args_1217_);
v___x_1220_ = lean_nat_dec_lt(v___x_1218_, v___x_1219_);
if (v___x_1220_ == 0)
{
v___y_1206_ = v___y_1169_;
goto v___jp_1205_;
}
else
{
if (v___x_1220_ == 0)
{
v___y_1206_ = v___y_1169_;
goto v___jp_1205_;
}
else
{
size_t v___x_1221_; size_t v___x_1222_; uint8_t v___x_1223_; 
v___x_1221_ = ((size_t)0ULL);
v___x_1222_ = lean_usize_of_nat(v___x_1219_);
v___x_1223_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1(v_args_1217_, v___x_1221_, v___x_1222_);
if (v___x_1223_ == 0)
{
v___y_1206_ = v___y_1169_;
goto v___jp_1205_;
}
else
{
uint8_t v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = 0;
v___x_1225_ = lean_box(v___x_1224_);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
return v___x_1226_;
}
}
}
}
else
{
v___y_1206_ = v___y_1169_;
goto v___jp_1205_;
}
v___jp_1173_:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_1171_, v___y_1174_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1196_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1196_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1196_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
if (lean_obj_tag(v_a_1176_) == 0)
{
if (lean_obj_tag(v_value_1172_) == 2)
{
lean_object* v_struct_1180_; uint8_t v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1184_; 
v_struct_1180_ = lean_ctor_get(v_value_1172_, 2);
v___x_1181_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg(v_struct_1180_, v_candidates_1165_);
v___x_1182_ = lean_box(v___x_1181_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1182_);
v___x_1184_ = v___x_1178_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
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
uint8_t v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1186_ = 0;
v___x_1187_ = lean_box(v___x_1186_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1187_);
v___x_1189_ = v___x_1178_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
else
{
uint8_t v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
lean_dec_ref(v_a_1176_);
v___x_1191_ = 1;
v___x_1192_ = lean_box(v___x_1191_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1192_);
v___x_1194_ = v___x_1178_;
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
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
v_a_1197_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1175_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1175_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
v___jp_1205_:
{
if (lean_obj_tag(v_value_1172_) == 4)
{
lean_object* v_args_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v_args_1207_ = lean_ctor_get(v_value_1172_, 1);
v___x_1208_ = lean_unsigned_to_nat(0u);
v___x_1209_ = lean_array_get_size(v_args_1207_);
v___x_1210_ = lean_nat_dec_lt(v___x_1208_, v___x_1209_);
if (v___x_1210_ == 0)
{
v___y_1174_ = v___y_1206_;
goto v___jp_1173_;
}
else
{
if (v___x_1210_ == 0)
{
v___y_1174_ = v___y_1206_;
goto v___jp_1173_;
}
else
{
size_t v___x_1211_; size_t v___x_1212_; uint8_t v___x_1213_; 
v___x_1211_ = ((size_t)0ULL);
v___x_1212_ = lean_usize_of_nat(v___x_1209_);
v___x_1213_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1(v_args_1207_, v___x_1211_, v___x_1212_);
if (v___x_1213_ == 0)
{
v___y_1174_ = v___y_1206_;
goto v___jp_1173_;
}
else
{
uint8_t v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = 0;
v___x_1215_ = lean_box(v___x_1214_);
v___x_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
return v___x_1216_;
}
}
}
}
else
{
v___y_1174_ = v___y_1206_;
goto v___jp_1173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullInstances___lam__0___boxed(lean_object* v_letDecl_1227_, lean_object* v_candidates_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_Compiler_LCNF_Decl_pullInstances___lam__0(v_letDecl_1227_, v_candidates_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v_candidates_1228_);
lean_dec_ref(v_letDecl_1227_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullInstances(lean_object* v_decl_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v___f_1242_; lean_object* v___x_1243_; 
v___f_1242_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_pullInstances___closed__0));
v___x_1243_ = l_Lean_Compiler_LCNF_Decl_pullLetDecls(v_decl_1236_, v___f_1242_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullInstances___boxed(lean_object* v_decl_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_Compiler_LCNF_Decl_pullInstances(v_decl_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
return v_res_1250_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0(lean_object* v_00_u03b2_1251_, lean_object* v_k_1252_, lean_object* v_t_1253_){
_start:
{
uint8_t v___x_1254_; 
v___x_1254_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg(v_k_1252_, v_t_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___boxed(lean_object* v_00_u03b2_1255_, lean_object* v_k_1256_, lean_object* v_t_1257_){
_start:
{
uint8_t v_res_1258_; lean_object* v_r_1259_; 
v_res_1258_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0(v_00_u03b2_1255_, v_k_1256_, v_t_1257_);
lean_dec(v_t_1257_);
lean_dec(v_k_1256_);
v_r_1259_ = lean_box(v_res_1258_);
return v_r_1259_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullInstances___closed__3(void){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1264_ = lean_unsigned_to_nat(0u);
v___x_1265_ = ((lean_object*)(l_Lean_Compiler_LCNF_pullInstances___closed__2));
v___x_1266_ = 0;
v___x_1267_ = ((lean_object*)(l_Lean_Compiler_LCNF_pullInstances___closed__1));
v___x_1268_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1267_, v___x_1266_, v___x_1265_, v___x_1264_);
return v___x_1268_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullInstances(void){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_obj_once(&l_Lean_Compiler_LCNF_pullInstances___closed__3, &l_Lean_Compiler_LCNF_pullInstances___closed__3_once, _init_l_Lean_Compiler_LCNF_pullInstances___closed__3);
return v___x_1269_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1325_ = lean_unsigned_to_nat(3825914912u);
v___x_1326_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_));
v___x_1327_ = l_Lean_Name_num___override(v___x_1326_, v___x_1325_);
return v___x_1327_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_));
v___x_1330_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_);
v___x_1331_ = l_Lean_Name_str___override(v___x_1330_, v___x_1329_);
return v___x_1331_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1333_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_));
v___x_1334_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_);
v___x_1335_ = l_Lean_Name_str___override(v___x_1334_, v___x_1333_);
return v___x_1335_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1336_ = lean_unsigned_to_nat(2u);
v___x_1337_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_);
v___x_1338_ = l_Lean_Name_num___override(v___x_1337_, v___x_1336_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1340_; uint8_t v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1340_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_));
v___x_1341_ = 1;
v___x_1342_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_);
v___x_1343_ = l_Lean_registerTraceClass(v___x_1340_, v___x_1341_, v___x_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2____boxed(lean_object* v_a_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_();
return v_res_1345_;
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
