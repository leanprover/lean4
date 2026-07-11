// Lean compiler output
// Module: Lean.Util.SCC
// Imports: public import Std.Data.HashMap.Basic public import Init.Data.Option.Coe
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
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_forM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
static const lean_ctor_object l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg___closed__0 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_push___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_push(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg___lam__0(lean_object*);
static const lean_closure_object l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg___closed__0 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__6 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__6_value;
static const lean_closure_object l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__5 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__4 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__3 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__2 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__1 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__1_value;
static const lean_closure_object l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__0 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__0_value),((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__1_value)}};
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__7 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__7_value),((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__2_value),((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__3_value),((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__4_value),((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__5_value)}};
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__8 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__8_value),((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__6_value)}};
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__9 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__9_value;
static const lean_closure_object l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_bind, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__18 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__18_value;
static const lean_closure_object l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__9, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__13 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__13_value;
static const lean_closure_object l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__7, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__12 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__12_value;
static const lean_closure_object l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__4, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__11 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__11_value;
static const lean_closure_object l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_pure, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__16 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__16_value;
static const lean_closure_object l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__10 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__10_value;
static const lean_closure_object l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_map, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__14 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__14_value;
static const lean_ctor_object l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__14_value),((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__10_value)}};
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__15 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__15_value;
static const lean_ctor_object l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__15_value),((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__16_value),((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__11_value),((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__12_value),((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__13_value)}};
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__17 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__17_value;
static const lean_ctor_object l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__17_value),((lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__18_value)}};
static const lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__19 = (const lean_object*)&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__19_value;
static lean_once_cell_t l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__20;
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SCC_scc___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_SCC_scc___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SCC_scc___redArg___closed__0;
static lean_once_cell_t l_Lean_SCC_scc___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SCC_scc___redArg___closed__1;
static lean_once_cell_t l_Lean_SCC_scc___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SCC_scc___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_SCC_scc___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SCC_scc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg(lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
lean_object* v_data_8_; lean_object* v___x_9_; 
v_data_8_ = lean_ctor_get(v_a_7_, 2);
v___x_9_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_4_, v_inst_5_, v_data_8_, v_a_6_);
if (lean_obj_tag(v___x_9_) == 0)
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = ((lean_object*)(l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg___closed__0));
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v_a_7_);
return v___x_11_;
}
else
{
lean_object* v_val_12_; lean_object* v___x_13_; 
v_val_12_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_val_12_);
lean_dec_ref_known(v___x_9_, 1);
v___x_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_13_, 0, v_val_12_);
lean_ctor_set(v___x_13_, 1, v_a_7_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf(lean_object* v_00_u03b1_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_a_17_, lean_object* v_a_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg(v_inst_15_, v_inst_16_, v_a_17_, v_a_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_push___redArg(lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v_stack_24_; lean_object* v_nextIndex_25_; lean_object* v_data_26_; lean_object* v_sccs_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_43_; 
v_stack_24_ = lean_ctor_get(v_a_23_, 0);
v_nextIndex_25_ = lean_ctor_get(v_a_23_, 1);
v_data_26_ = lean_ctor_get(v_a_23_, 2);
v_sccs_27_ = lean_ctor_get(v_a_23_, 3);
v_isSharedCheck_43_ = !lean_is_exclusive(v_a_23_);
if (v_isSharedCheck_43_ == 0)
{
v___x_29_ = v_a_23_;
v_isShared_30_ = v_isSharedCheck_43_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_sccs_27_);
lean_inc(v_data_26_);
lean_inc(v_nextIndex_25_);
lean_inc(v_stack_24_);
lean_dec(v_a_23_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_43_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
v___x_31_ = lean_box(0);
lean_inc(v_a_22_);
v___x_32_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_32_, 0, v_a_22_);
lean_ctor_set(v___x_32_, 1, v_stack_24_);
v___x_33_ = lean_unsigned_to_nat(1u);
v___x_34_ = lean_nat_add(v_nextIndex_25_, v___x_33_);
v___x_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_35_, 0, v_nextIndex_25_);
v___x_36_ = 1;
lean_inc_ref(v___x_35_);
v___x_37_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_37_, 0, v___x_35_);
lean_ctor_set(v___x_37_, 1, v___x_35_);
lean_ctor_set_uint8(v___x_37_, sizeof(void*)*2, v___x_36_);
v___x_38_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_20_, v_inst_21_, v_data_26_, v_a_22_, v___x_37_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 2, v___x_38_);
lean_ctor_set(v___x_29_, 1, v___x_34_);
lean_ctor_set(v___x_29_, 0, v___x_32_);
v___x_40_ = v___x_29_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_32_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v___x_34_);
lean_ctor_set(v_reuseFailAlloc_42_, 2, v___x_38_);
lean_ctor_set(v_reuseFailAlloc_42_, 3, v_sccs_27_);
v___x_40_ = v_reuseFailAlloc_42_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_41_; 
v___x_41_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_41_, 0, v___x_31_);
lean_ctor_set(v___x_41_, 1, v___x_40_);
return v___x_41_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_push(lean_object* v_00_u03b1_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l___private_Lean_Util_SCC_0__Lean_SCC_push___redArg(v_inst_45_, v_inst_46_, v_a_47_, v_a_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___redArg(lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_a_52_, lean_object* v_f_53_, lean_object* v_a_54_){
_start:
{
lean_object* v_stack_55_; lean_object* v_nextIndex_56_; lean_object* v_data_57_; lean_object* v_sccs_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_73_; 
v_stack_55_ = lean_ctor_get(v_a_54_, 0);
v_nextIndex_56_ = lean_ctor_get(v_a_54_, 1);
v_data_57_ = lean_ctor_get(v_a_54_, 2);
v_sccs_58_ = lean_ctor_get(v_a_54_, 3);
v_isSharedCheck_73_ = !lean_is_exclusive(v_a_54_);
if (v_isSharedCheck_73_ == 0)
{
v___x_60_ = v_a_54_;
v_isShared_61_ = v_isSharedCheck_73_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_sccs_58_);
lean_inc(v_data_57_);
lean_inc(v_nextIndex_56_);
lean_inc(v_stack_55_);
lean_dec(v_a_54_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_73_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_62_; lean_object* v___y_64_; lean_object* v___x_69_; 
v___x_62_ = lean_box(0);
lean_inc(v_a_52_);
lean_inc_ref(v_inst_51_);
lean_inc_ref(v_inst_50_);
v___x_69_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_50_, v_inst_51_, v_data_57_, v_a_52_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_dec_ref(v_f_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_inst_51_);
lean_dec_ref(v_inst_50_);
v___y_64_ = v_data_57_;
goto v___jp_63_;
}
else
{
lean_object* v_val_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_val_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc(v_val_70_);
lean_dec_ref_known(v___x_69_, 1);
v___x_71_ = lean_apply_1(v_f_53_, v_val_70_);
v___x_72_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_50_, v_inst_51_, v_data_57_, v_a_52_, v___x_71_);
v___y_64_ = v___x_72_;
goto v___jp_63_;
}
v___jp_63_:
{
lean_object* v___x_66_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 2, v___y_64_);
v___x_66_ = v___x_60_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_stack_55_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_nextIndex_56_);
lean_ctor_set(v_reuseFailAlloc_68_, 2, v___y_64_);
lean_ctor_set(v_reuseFailAlloc_68_, 3, v_sccs_58_);
v___x_66_ = v_reuseFailAlloc_68_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_67_; 
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_62_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
return v___x_67_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf(lean_object* v_00_u03b1_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_a_77_, lean_object* v_f_78_, lean_object* v_a_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___redArg(v_inst_75_, v_inst_76_, v_a_77_, v_f_78_, v_a_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg___lam__0(lean_object* v_d_81_){
_start:
{
lean_object* v_index_x3f_82_; lean_object* v_lowlink_x3f_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_91_; 
v_index_x3f_82_ = lean_ctor_get(v_d_81_, 0);
v_lowlink_x3f_83_ = lean_ctor_get(v_d_81_, 1);
v_isSharedCheck_91_ = !lean_is_exclusive(v_d_81_);
if (v_isSharedCheck_91_ == 0)
{
v___x_85_ = v_d_81_;
v_isShared_86_ = v_isSharedCheck_91_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_lowlink_x3f_83_);
lean_inc(v_index_x3f_82_);
lean_dec(v_d_81_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_91_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
uint8_t v___x_87_; lean_object* v___x_89_; 
v___x_87_ = 0;
if (v_isShared_86_ == 0)
{
v___x_89_ = v___x_85_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_index_x3f_82_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v_lowlink_x3f_83_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*2, v___x_87_);
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg(lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v___f_97_; lean_object* v___x_98_; 
v___f_97_ = ((lean_object*)(l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg___closed__0));
v___x_98_ = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___redArg(v_inst_93_, v_inst_94_, v_a_95_, v___f_97_, v_a_96_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack(lean_object* v_00_u03b1_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg(v_inst_100_, v_inst_101_, v_a_102_, v_a_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___redArg___lam__0(lean_object* v_v_105_, lean_object* v_d_106_){
_start:
{
if (lean_obj_tag(v_v_105_) == 0)
{
return v_d_106_;
}
else
{
lean_object* v_lowlink_x3f_107_; 
v_lowlink_x3f_107_ = lean_ctor_get(v_d_106_, 1);
if (lean_obj_tag(v_lowlink_x3f_107_) == 0)
{
lean_object* v_index_x3f_108_; uint8_t v_onStack_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
v_index_x3f_108_ = lean_ctor_get(v_d_106_, 0);
v_onStack_109_ = lean_ctor_get_uint8(v_d_106_, sizeof(void*)*2);
v_isSharedCheck_116_ = !lean_is_exclusive(v_d_106_);
if (v_isSharedCheck_116_ == 0)
{
lean_object* v_unused_117_; 
v_unused_117_ = lean_ctor_get(v_d_106_, 1);
lean_dec(v_unused_117_);
v___x_111_ = v_d_106_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_index_x3f_108_);
lean_dec(v_d_106_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 1, v_v_105_);
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_index_x3f_108_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v_v_105_);
lean_ctor_set_uint8(v_reuseFailAlloc_115_, sizeof(void*)*2, v_onStack_109_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
else
{
lean_object* v_index_x3f_118_; uint8_t v_onStack_119_; lean_object* v_val_120_; lean_object* v_val_121_; uint8_t v___x_122_; 
v_index_x3f_118_ = lean_ctor_get(v_d_106_, 0);
v_onStack_119_ = lean_ctor_get_uint8(v_d_106_, sizeof(void*)*2);
v_val_120_ = lean_ctor_get(v_v_105_, 0);
v_val_121_ = lean_ctor_get(v_lowlink_x3f_107_, 0);
v___x_122_ = lean_nat_dec_lt(v_val_121_, v_val_120_);
if (v___x_122_ == 0)
{
lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
lean_inc(v_index_x3f_118_);
v_isSharedCheck_129_ = !lean_is_exclusive(v_d_106_);
if (v_isSharedCheck_129_ == 0)
{
lean_object* v_unused_130_; lean_object* v_unused_131_; 
v_unused_130_ = lean_ctor_get(v_d_106_, 1);
lean_dec(v_unused_130_);
v_unused_131_ = lean_ctor_get(v_d_106_, 0);
lean_dec(v_unused_131_);
v___x_124_ = v_d_106_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_dec(v_d_106_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 1, v_v_105_);
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_index_x3f_118_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_v_105_);
lean_ctor_set_uint8(v_reuseFailAlloc_128_, sizeof(void*)*2, v_onStack_119_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
else
{
lean_dec_ref_known(v_v_105_, 1);
return v_d_106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___redArg(lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_a_134_, lean_object* v_v_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___f_137_; lean_object* v___x_138_; 
v___f_137_ = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___redArg___lam__0), 2, 1);
lean_closure_set(v___f_137_, 0, v_v_135_);
v___x_138_ = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___redArg(v_inst_132_, v_inst_133_, v_a_134_, v___f_137_, v_a_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf(lean_object* v_00_u03b1_139_, lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_a_142_, lean_object* v_v_143_, lean_object* v_a_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___redArg(v_inst_140_, v_inst_141_, v_a_142_, v_v_143_, v_a_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___redArg(lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_a_148_, lean_object* v_x_149_, lean_object* v_x_150_, lean_object* v_a_151_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
lean_object* v_nextIndex_152_; lean_object* v_data_153_; lean_object* v_sccs_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_164_; 
lean_dec(v_a_148_);
lean_dec_ref(v_inst_147_);
lean_dec_ref(v_inst_146_);
v_nextIndex_152_ = lean_ctor_get(v_a_151_, 1);
v_data_153_ = lean_ctor_get(v_a_151_, 2);
v_sccs_154_ = lean_ctor_get(v_a_151_, 3);
v_isSharedCheck_164_ = !lean_is_exclusive(v_a_151_);
if (v_isSharedCheck_164_ == 0)
{
lean_object* v_unused_165_; 
v_unused_165_ = lean_ctor_get(v_a_151_, 0);
lean_dec(v_unused_165_);
v___x_156_ = v_a_151_;
v_isShared_157_ = v_isSharedCheck_164_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_sccs_154_);
lean_inc(v_data_153_);
lean_inc(v_nextIndex_152_);
lean_dec(v_a_151_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_164_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_161_; 
v___x_158_ = lean_box(0);
v___x_159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_159_, 0, v_x_150_);
lean_ctor_set(v___x_159_, 1, v_sccs_154_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 3, v___x_159_);
lean_ctor_set(v___x_156_, 0, v_x_149_);
v___x_161_ = v___x_156_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_x_149_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_nextIndex_152_);
lean_ctor_set(v_reuseFailAlloc_163_, 2, v_data_153_);
lean_ctor_set(v_reuseFailAlloc_163_, 3, v___x_159_);
v___x_161_ = v_reuseFailAlloc_163_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
lean_object* v___x_162_; 
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_158_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
return v___x_162_;
}
}
}
else
{
lean_object* v_head_166_; lean_object* v_tail_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_201_; 
v_head_166_ = lean_ctor_get(v_x_149_, 0);
v_tail_167_ = lean_ctor_get(v_x_149_, 1);
v_isSharedCheck_201_ = !lean_is_exclusive(v_x_149_);
if (v_isSharedCheck_201_ == 0)
{
v___x_169_ = v_x_149_;
v_isShared_170_ = v_isSharedCheck_201_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_tail_167_);
lean_inc(v_head_166_);
lean_dec(v_x_149_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_201_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v_snd_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_199_; 
lean_inc(v_head_166_);
lean_inc_ref(v_inst_147_);
lean_inc_ref(v_inst_146_);
v___x_171_ = l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg(v_inst_146_, v_inst_147_, v_head_166_, v_a_151_);
v_snd_172_ = lean_ctor_get(v___x_171_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_199_ == 0)
{
lean_object* v_unused_200_; 
v_unused_200_ = lean_ctor_get(v___x_171_, 0);
lean_dec(v_unused_200_);
v___x_174_ = v___x_171_;
v_isShared_175_ = v_isSharedCheck_199_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_snd_172_);
lean_dec(v___x_171_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_199_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
lean_inc(v_head_166_);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 1, v_x_150_);
v___x_177_ = v___x_169_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_head_166_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_x_150_);
v___x_177_ = v_reuseFailAlloc_198_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_178_; uint8_t v___x_179_; uint8_t v___x_180_; 
lean_inc_ref(v_inst_146_);
lean_inc(v_a_148_);
v___x_178_ = lean_apply_2(v_inst_146_, v_a_148_, v_head_166_);
v___x_179_ = lean_unbox(v___x_178_);
v___x_180_ = lean_bool_not(v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v_nextIndex_181_; lean_object* v_data_182_; lean_object* v_sccs_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_195_; 
lean_dec(v_a_148_);
lean_dec_ref(v_inst_147_);
lean_dec_ref(v_inst_146_);
v_nextIndex_181_ = lean_ctor_get(v_snd_172_, 1);
v_data_182_ = lean_ctor_get(v_snd_172_, 2);
v_sccs_183_ = lean_ctor_get(v_snd_172_, 3);
v_isSharedCheck_195_ = !lean_is_exclusive(v_snd_172_);
if (v_isSharedCheck_195_ == 0)
{
lean_object* v_unused_196_; 
v_unused_196_ = lean_ctor_get(v_snd_172_, 0);
lean_dec(v_unused_196_);
v___x_185_ = v_snd_172_;
v_isShared_186_ = v_isSharedCheck_195_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_sccs_183_);
lean_inc(v_data_182_);
lean_inc(v_nextIndex_181_);
lean_dec(v_snd_172_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_195_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_187_ = lean_box(0);
v___x_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_177_);
lean_ctor_set(v___x_188_, 1, v_sccs_183_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 3, v___x_188_);
lean_ctor_set(v___x_185_, 0, v_tail_167_);
v___x_190_ = v___x_185_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_tail_167_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_nextIndex_181_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v_data_182_);
lean_ctor_set(v_reuseFailAlloc_194_, 3, v___x_188_);
v___x_190_ = v_reuseFailAlloc_194_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_192_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v___x_190_);
lean_ctor_set(v___x_174_, 0, v___x_187_);
v___x_192_ = v___x_174_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
else
{
lean_del_object(v___x_174_);
v_x_149_ = v_tail_167_;
v_x_150_ = v___x_177_;
v_a_151_ = v_snd_172_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add(lean_object* v_00_u03b1_202_, lean_object* v_inst_203_, lean_object* v_inst_204_, lean_object* v_a_205_, lean_object* v_x_206_, lean_object* v_x_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___redArg(v_inst_203_, v_inst_204_, v_a_205_, v_x_206_, v_x_207_, v_a_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___redArg(lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_stack_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_stack_214_ = lean_ctor_get(v_a_213_, 0);
lean_inc(v_stack_214_);
v___x_215_ = lean_box(0);
v___x_216_ = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___redArg(v_inst_210_, v_inst_211_, v_a_212_, v_stack_214_, v___x_215_, v_a_213_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC(lean_object* v_00_u03b1_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___redArg(v_inst_218_, v_inst_219_, v_a_220_, v_a_221_);
return v___x_222_;
}
}
static lean_object* _init_l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__20(void){
_start:
{
lean_object* v___x_268_; lean_object* v___f_269_; 
v___x_268_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_269_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_269_, 0, v___x_268_);
return v___f_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg(lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_successorsOf_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v_snd_277_; lean_object* v___f_278_; lean_object* v___x_279_; lean_object* v___x_1010__overap_280_; lean_object* v___x_281_; lean_object* v_snd_282_; lean_object* v___x_283_; lean_object* v_fst_284_; lean_object* v_snd_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_298_; 
v___x_275_ = ((lean_object*)(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__19));
lean_inc_n(v_a_273_, 4);
lean_inc_ref_n(v_inst_271_, 3);
lean_inc_ref_n(v_inst_270_, 3);
v___x_276_ = l___private_Lean_Util_SCC_0__Lean_SCC_push___redArg(v_inst_270_, v_inst_271_, v_a_273_, v_a_274_);
v_snd_277_ = lean_ctor_get(v___x_276_, 1);
lean_inc(v_snd_277_);
lean_dec_ref(v___x_276_);
lean_inc_ref(v_successorsOf_272_);
v___f_278_ = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___lam__0), 6, 4);
lean_closure_set(v___f_278_, 0, v_inst_270_);
lean_closure_set(v___f_278_, 1, v_inst_271_);
lean_closure_set(v___f_278_, 2, v_successorsOf_272_);
lean_closure_set(v___f_278_, 3, v_a_273_);
v___x_279_ = lean_apply_1(v_successorsOf_272_, v_a_273_);
v___x_1010__overap_280_ = l_List_forM___redArg(v___x_275_, v___x_279_, v___f_278_);
v___x_281_ = lean_apply_1(v___x_1010__overap_280_, v_snd_277_);
v_snd_282_ = lean_ctor_get(v___x_281_, 1);
lean_inc(v_snd_282_);
lean_dec_ref(v___x_281_);
v___x_283_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg(v_inst_270_, v_inst_271_, v_a_273_, v_snd_282_);
v_fst_284_ = lean_ctor_get(v___x_283_, 0);
v_snd_285_ = lean_ctor_get(v___x_283_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_298_ == 0)
{
v___x_287_ = v___x_283_;
v_isShared_288_ = v_isSharedCheck_298_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_snd_285_);
lean_inc(v_fst_284_);
lean_dec(v___x_283_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_298_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v_index_x3f_289_; lean_object* v_lowlink_x3f_290_; lean_object* v___f_291_; uint8_t v___x_292_; 
v_index_x3f_289_ = lean_ctor_get(v_fst_284_, 0);
lean_inc(v_index_x3f_289_);
v_lowlink_x3f_290_ = lean_ctor_get(v_fst_284_, 1);
lean_inc(v_lowlink_x3f_290_);
lean_dec(v_fst_284_);
v___f_291_ = lean_obj_once(&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__20, &l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__20_once, _init_l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__20);
v___x_292_ = l_Option_instBEq_beq___redArg(v___f_291_, v_lowlink_x3f_290_, v_index_x3f_289_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_295_; 
lean_dec(v_a_273_);
lean_dec_ref(v_inst_271_);
lean_dec_ref(v_inst_270_);
v___x_293_ = lean_box(0);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_293_);
v___x_295_ = v___x_287_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_snd_285_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
else
{
lean_object* v___x_297_; 
lean_del_object(v___x_287_);
v___x_297_ = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___redArg(v_inst_270_, v_inst_271_, v_a_273_, v_snd_285_);
return v___x_297_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___lam__0(lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_successorsOf_301_, lean_object* v_a_302_, lean_object* v_b_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_305_; lean_object* v_fst_306_; lean_object* v_index_x3f_307_; 
lean_inc(v_b_303_);
lean_inc_ref(v_inst_300_);
lean_inc_ref(v_inst_299_);
v___x_305_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg(v_inst_299_, v_inst_300_, v_b_303_, v___y_304_);
v_fst_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_fst_306_);
v_index_x3f_307_ = lean_ctor_get(v_fst_306_, 0);
lean_inc(v_index_x3f_307_);
if (lean_obj_tag(v_index_x3f_307_) == 0)
{
lean_object* v_snd_308_; lean_object* v___x_309_; lean_object* v_snd_310_; lean_object* v___x_311_; lean_object* v_fst_312_; lean_object* v_snd_313_; lean_object* v_lowlink_x3f_314_; lean_object* v___x_315_; 
lean_dec(v_fst_306_);
v_snd_308_ = lean_ctor_get(v___x_305_, 1);
lean_inc(v_snd_308_);
lean_dec_ref(v___x_305_);
lean_inc(v_b_303_);
lean_inc_ref_n(v_inst_300_, 2);
lean_inc_ref_n(v_inst_299_, 2);
v___x_309_ = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg(v_inst_299_, v_inst_300_, v_successorsOf_301_, v_b_303_, v_snd_308_);
v_snd_310_ = lean_ctor_get(v___x_309_, 1);
lean_inc(v_snd_310_);
lean_dec_ref(v___x_309_);
v___x_311_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg(v_inst_299_, v_inst_300_, v_b_303_, v_snd_310_);
v_fst_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_fst_312_);
v_snd_313_ = lean_ctor_get(v___x_311_, 1);
lean_inc(v_snd_313_);
lean_dec_ref(v___x_311_);
v_lowlink_x3f_314_ = lean_ctor_get(v_fst_312_, 1);
lean_inc(v_lowlink_x3f_314_);
lean_dec(v_fst_312_);
v___x_315_ = l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___redArg(v_inst_299_, v_inst_300_, v_a_302_, v_lowlink_x3f_314_, v_snd_313_);
return v___x_315_;
}
else
{
uint8_t v_onStack_316_; 
lean_dec(v_b_303_);
lean_dec_ref(v_successorsOf_301_);
v_onStack_316_ = lean_ctor_get_uint8(v_fst_306_, sizeof(void*)*2);
lean_dec(v_fst_306_);
if (v_onStack_316_ == 0)
{
lean_object* v_snd_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_325_; 
lean_dec_ref_known(v_index_x3f_307_, 1);
lean_dec(v_a_302_);
lean_dec_ref(v_inst_300_);
lean_dec_ref(v_inst_299_);
v_snd_317_ = lean_ctor_get(v___x_305_, 1);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_325_ == 0)
{
lean_object* v_unused_326_; 
v_unused_326_ = lean_ctor_get(v___x_305_, 0);
lean_dec(v_unused_326_);
v___x_319_ = v___x_305_;
v_isShared_320_ = v_isSharedCheck_325_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_snd_317_);
lean_dec(v___x_305_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_325_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_321_ = lean_box(0);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_321_);
v___x_323_ = v___x_319_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_snd_317_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
else
{
lean_object* v_snd_327_; lean_object* v___x_328_; 
v_snd_327_ = lean_ctor_get(v___x_305_, 1);
lean_inc(v_snd_327_);
lean_dec_ref(v___x_305_);
v___x_328_ = l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___redArg(v_inst_299_, v_inst_300_, v_a_302_, v_index_x3f_307_, v_snd_327_);
return v___x_328_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux(lean_object* v_00_u03b1_329_, lean_object* v_inst_330_, lean_object* v_inst_331_, lean_object* v_successorsOf_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg(v_inst_330_, v_inst_331_, v_successorsOf_332_, v_a_333_, v_a_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_SCC_scc___redArg___lam__0(lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_successorsOf_338_, lean_object* v_a_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___x_341_; lean_object* v_fst_342_; lean_object* v_index_x3f_343_; 
lean_inc(v_a_339_);
lean_inc_ref(v_inst_337_);
lean_inc_ref(v_inst_336_);
v___x_341_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg(v_inst_336_, v_inst_337_, v_a_339_, v___y_340_);
v_fst_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_fst_342_);
v_index_x3f_343_ = lean_ctor_get(v_fst_342_, 0);
lean_inc(v_index_x3f_343_);
lean_dec(v_fst_342_);
if (lean_obj_tag(v_index_x3f_343_) == 0)
{
lean_object* v_snd_344_; lean_object* v___x_345_; 
v_snd_344_ = lean_ctor_get(v___x_341_, 1);
lean_inc(v_snd_344_);
lean_dec_ref(v___x_341_);
v___x_345_ = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg(v_inst_336_, v_inst_337_, v_successorsOf_338_, v_a_339_, v_snd_344_);
return v___x_345_;
}
else
{
lean_object* v_snd_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_354_; 
lean_dec_ref_known(v_index_x3f_343_, 1);
lean_dec(v_a_339_);
lean_dec_ref(v_successorsOf_338_);
lean_dec_ref(v_inst_337_);
lean_dec_ref(v_inst_336_);
v_snd_346_ = lean_ctor_get(v___x_341_, 1);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; 
v_unused_355_ = lean_ctor_get(v___x_341_, 0);
lean_dec(v_unused_355_);
v___x_348_ = v___x_341_;
v_isShared_349_ = v_isSharedCheck_354_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_snd_346_);
lean_dec(v___x_341_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_354_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = lean_box(0);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_350_);
v___x_352_ = v___x_348_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_snd_346_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
static lean_object* _init_l_Lean_SCC_scc___redArg___closed__0(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = lean_box(0);
v___x_357_ = lean_unsigned_to_nat(16u);
v___x_358_ = lean_mk_array(v___x_357_, v___x_356_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_SCC_scc___redArg___closed__1(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = lean_obj_once(&l_Lean_SCC_scc___redArg___closed__0, &l_Lean_SCC_scc___redArg___closed__0_once, _init_l_Lean_SCC_scc___redArg___closed__0);
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_SCC_scc___redArg___closed__2(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_362_ = lean_obj_once(&l_Lean_SCC_scc___redArg___closed__1, &l_Lean_SCC_scc___redArg___closed__1_once, _init_l_Lean_SCC_scc___redArg___closed__1);
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = lean_box(0);
v___x_365_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___x_363_);
lean_ctor_set(v___x_365_, 2, v___x_362_);
lean_ctor_set(v___x_365_, 3, v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_SCC_scc___redArg(lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_vertices_368_, lean_object* v_successorsOf_369_){
_start:
{
lean_object* v___f_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_385__overap_373_; lean_object* v___x_374_; lean_object* v_snd_375_; lean_object* v_sccs_376_; lean_object* v___x_377_; 
v___f_370_ = lean_alloc_closure((void*)(l_Lean_SCC_scc___redArg___lam__0), 5, 3);
lean_closure_set(v___f_370_, 0, v_inst_366_);
lean_closure_set(v___f_370_, 1, v_inst_367_);
lean_closure_set(v___f_370_, 2, v_successorsOf_369_);
v___x_371_ = ((lean_object*)(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__19));
v___x_372_ = lean_obj_once(&l_Lean_SCC_scc___redArg___closed__2, &l_Lean_SCC_scc___redArg___closed__2_once, _init_l_Lean_SCC_scc___redArg___closed__2);
v___x_385__overap_373_ = l_List_forM___redArg(v___x_371_, v_vertices_368_, v___f_370_);
v___x_374_ = lean_apply_1(v___x_385__overap_373_, v___x_372_);
v_snd_375_ = lean_ctor_get(v___x_374_, 1);
lean_inc(v_snd_375_);
lean_dec_ref(v___x_374_);
v_sccs_376_ = lean_ctor_get(v_snd_375_, 3);
lean_inc(v_sccs_376_);
lean_dec(v_snd_375_);
v___x_377_ = l_List_reverse___redArg(v_sccs_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_SCC_scc(lean_object* v_00_u03b1_378_, lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_vertices_381_, lean_object* v_successorsOf_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_SCC_scc___redArg(v_inst_379_, v_inst_380_, v_vertices_381_, v_successorsOf_382_);
return v___x_383_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_SCC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_SCC(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Coe(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_SCC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_SCC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_SCC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_SCC(builtin);
}
#ifdef __cplusplus
}
#endif
