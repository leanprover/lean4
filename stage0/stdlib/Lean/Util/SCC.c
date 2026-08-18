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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
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
static lean_once_cell_t l_Lean_SCC_scc___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SCC_scc___redArg___closed__3;
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
lean_object* v_stack_24_; lean_object* v_nextIndex_25_; lean_object* v_data_26_; lean_object* v_sccs_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_104_; 
v_stack_24_ = lean_ctor_get(v_a_23_, 0);
v_nextIndex_25_ = lean_ctor_get(v_a_23_, 1);
v_data_26_ = lean_ctor_get(v_a_23_, 2);
v_sccs_27_ = lean_ctor_get(v_a_23_, 3);
v_isSharedCheck_104_ = !lean_is_exclusive(v_a_23_);
if (v_isSharedCheck_104_ == 0)
{
v___x_29_ = v_a_23_;
v_isShared_30_ = v_isSharedCheck_104_;
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
v_isShared_30_ = v_isSharedCheck_104_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___y_36_; lean_object* v___x_41_; uint8_t v___x_42_; lean_object* v___x_43_; lean_object* v___y_45_; lean_object* v_i_46_; lean_object* v___y_51_; lean_object* v___y_61_; lean_object* v_i_62_; lean_object* v___x_76_; 
v___x_31_ = lean_box(0);
lean_inc_n(v_a_22_, 2);
v___x_32_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_32_, 0, v_a_22_);
lean_ctor_set(v___x_32_, 1, v_stack_24_);
v___x_33_ = lean_unsigned_to_nat(1u);
v___x_34_ = lean_nat_add(v_nextIndex_25_, v___x_33_);
v___x_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_41_, 0, v_nextIndex_25_);
v___x_42_ = 1;
lean_inc_ref(v___x_41_);
v___x_43_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_43_, 0, v___x_41_);
lean_ctor_set(v___x_43_, 1, v___x_41_);
lean_ctor_set_uint8(v___x_43_, sizeof(void*)*2, v___x_42_);
lean_inc_ref(v_inst_21_);
lean_inc_ref(v_inst_20_);
v___x_76_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_20_, v_inst_21_, v_data_26_, v_a_22_);
switch(lean_obj_tag(v___x_76_))
{
case 0:
{
lean_object* v_index_77_; lean_object* v_size_78_; lean_object* v___x_79_; 
lean_dec_ref(v_inst_21_);
lean_dec_ref(v_inst_20_);
v_index_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_index_77_);
lean_dec_ref_known(v___x_76_, 3);
v_size_78_ = lean_ctor_get(v_data_26_, 0);
lean_inc(v_size_78_);
v___x_79_ = l_Std_DHashMap_Raw_setEntry___redArg(v_data_26_, v_size_78_, v_index_77_, v_a_22_, v___x_43_);
lean_dec(v_index_77_);
v___y_36_ = v___x_79_;
goto v___jp_35_;
}
case 1:
{
lean_object* v_index_80_; lean_object* v_size_81_; lean_object* v_keyArray_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v_index_80_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_index_80_);
lean_dec_ref_known(v___x_76_, 1);
v_size_81_ = lean_ctor_get(v_data_26_, 0);
v_keyArray_82_ = lean_ctor_get(v_data_26_, 1);
v___x_83_ = lean_nat_add(v_size_81_, v___x_33_);
v___x_84_ = lean_array_get_size(v_keyArray_82_);
v___x_85_ = lean_nat_dec_lt(v___x_83_, v___x_84_);
if (v___x_85_ == 0)
{
lean_dec(v___x_83_);
lean_dec(v_index_80_);
goto v___jp_66_;
}
else
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_86_ = lean_unsigned_to_nat(4u);
v___x_87_ = lean_nat_mul(v___x_83_, v___x_86_);
v___x_88_ = lean_unsigned_to_nat(3u);
v___x_89_ = lean_nat_mul(v___x_84_, v___x_88_);
v___x_90_ = lean_nat_dec_le(v___x_87_, v___x_89_);
lean_dec(v___x_89_);
lean_dec(v___x_87_);
if (v___x_90_ == 0)
{
lean_dec(v___x_83_);
lean_dec(v_index_80_);
goto v___jp_66_;
}
else
{
lean_object* v___x_91_; 
lean_dec_ref(v_inst_21_);
lean_dec_ref(v_inst_20_);
v___x_91_ = l_Std_DHashMap_Raw_setEntry___redArg(v_data_26_, v___x_83_, v_index_80_, v_a_22_, v___x_43_);
lean_dec(v_index_80_);
v___y_36_ = v___x_91_;
goto v___jp_35_;
}
}
}
default: 
{
lean_object* v_size_92_; lean_object* v_keyArray_93_; lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v_size_92_ = lean_ctor_get(v_data_26_, 0);
v_keyArray_93_ = lean_ctor_get(v_data_26_, 1);
v___x_94_ = lean_nat_add(v_size_92_, v___x_33_);
v___x_95_ = lean_array_get_size(v_keyArray_93_);
v___x_96_ = lean_nat_dec_lt(v___x_94_, v___x_95_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
lean_dec(v___x_94_);
lean_inc_ref(v_inst_21_);
lean_inc_ref(v_inst_20_);
v___x_97_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_20_, v_inst_21_, v_data_26_);
v___y_51_ = v___x_97_;
goto v___jp_50_;
}
else
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_98_ = lean_unsigned_to_nat(4u);
v___x_99_ = lean_nat_mul(v___x_94_, v___x_98_);
lean_dec(v___x_94_);
v___x_100_ = lean_unsigned_to_nat(3u);
v___x_101_ = lean_nat_mul(v___x_95_, v___x_100_);
v___x_102_ = lean_nat_dec_le(v___x_99_, v___x_101_);
lean_dec(v___x_101_);
lean_dec(v___x_99_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
lean_inc_ref(v_inst_21_);
lean_inc_ref(v_inst_20_);
v___x_103_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_20_, v_inst_21_, v_data_26_);
v___y_51_ = v___x_103_;
goto v___jp_50_;
}
else
{
v___y_51_ = v_data_26_;
goto v___jp_50_;
}
}
}
}
v___jp_35_:
{
lean_object* v___x_38_; 
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 2, v___y_36_);
lean_ctor_set(v___x_29_, 1, v___x_34_);
lean_ctor_set(v___x_29_, 0, v___x_32_);
v___x_38_ = v___x_29_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_32_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v___x_34_);
lean_ctor_set(v_reuseFailAlloc_40_, 2, v___y_36_);
lean_ctor_set(v_reuseFailAlloc_40_, 3, v_sccs_27_);
v___x_38_ = v_reuseFailAlloc_40_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
lean_object* v___x_39_; 
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_31_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
return v___x_39_;
}
}
v___jp_44_:
{
lean_object* v_size_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_size_47_ = lean_ctor_get(v___y_45_, 0);
v___x_48_ = lean_nat_add(v_size_47_, v___x_33_);
v___x_49_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_45_, v___x_48_, v_i_46_, v_a_22_, v___x_43_);
lean_dec(v_i_46_);
v___y_36_ = v___x_49_;
goto v___jp_35_;
}
v___jp_50_:
{
lean_object* v___x_52_; 
lean_inc(v_a_22_);
v___x_52_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_20_, v_inst_21_, v___y_51_, v_a_22_);
switch(lean_obj_tag(v___x_52_))
{
case 0:
{
lean_object* v_index_53_; lean_object* v_size_54_; lean_object* v___x_55_; 
v_index_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_index_53_);
lean_dec_ref_known(v___x_52_, 3);
v_size_54_ = lean_ctor_get(v___y_51_, 0);
lean_inc(v_size_54_);
v___x_55_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_51_, v_size_54_, v_index_53_, v_a_22_, v___x_43_);
lean_dec(v_index_53_);
v___y_36_ = v___x_55_;
goto v___jp_35_;
}
case 1:
{
lean_object* v_index_56_; 
v_index_56_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_index_56_);
lean_dec_ref_known(v___x_52_, 1);
v___y_45_ = v___y_51_;
v_i_46_ = v_index_56_;
goto v___jp_44_;
}
default: 
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_51_, v___x_57_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v_index_59_; 
v_index_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_index_59_);
lean_dec_ref_known(v___x_58_, 1);
v___y_45_ = v___y_51_;
v_i_46_ = v_index_59_;
goto v___jp_44_;
}
else
{
lean_dec_ref_known(v___x_43_, 2);
lean_dec(v_a_22_);
v___y_36_ = v___y_51_;
goto v___jp_35_;
}
}
}
}
v___jp_60_:
{
lean_object* v_size_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v_size_63_ = lean_ctor_get(v___y_61_, 0);
v___x_64_ = lean_nat_add(v_size_63_, v___x_33_);
v___x_65_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_61_, v___x_64_, v_i_62_, v_a_22_, v___x_43_);
lean_dec(v_i_62_);
v___y_36_ = v___x_65_;
goto v___jp_35_;
}
v___jp_66_:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_inc_ref(v_inst_21_);
lean_inc_ref(v_inst_20_);
v___x_67_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_20_, v_inst_21_, v_data_26_);
lean_inc(v_a_22_);
v___x_68_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_20_, v_inst_21_, v___x_67_, v_a_22_);
switch(lean_obj_tag(v___x_68_))
{
case 0:
{
lean_object* v_index_69_; lean_object* v_size_70_; lean_object* v___x_71_; 
v_index_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_index_69_);
lean_dec_ref_known(v___x_68_, 3);
v_size_70_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_size_70_);
v___x_71_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_67_, v_size_70_, v_index_69_, v_a_22_, v___x_43_);
lean_dec(v_index_69_);
v___y_36_ = v___x_71_;
goto v___jp_35_;
}
case 1:
{
lean_object* v_index_72_; 
v_index_72_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_index_72_);
lean_dec_ref_known(v___x_68_, 1);
v___y_61_ = v___x_67_;
v_i_62_ = v_index_72_;
goto v___jp_60_;
}
default: 
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_67_, v___x_73_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_index_75_; 
v_index_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_index_75_);
lean_dec_ref_known(v___x_74_, 1);
v___y_61_ = v___x_67_;
v_i_62_ = v_index_75_;
goto v___jp_60_;
}
else
{
lean_dec_ref_known(v___x_43_, 2);
lean_dec(v_a_22_);
v___y_36_ = v___x_67_;
goto v___jp_35_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_push(lean_object* v_00_u03b1_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l___private_Lean_Util_SCC_0__Lean_SCC_push___redArg(v_inst_106_, v_inst_107_, v_a_108_, v_a_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___redArg(lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_a_113_, lean_object* v_f_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_stack_116_; lean_object* v_nextIndex_117_; lean_object* v_data_118_; lean_object* v_sccs_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_197_; 
v_stack_116_ = lean_ctor_get(v_a_115_, 0);
v_nextIndex_117_ = lean_ctor_get(v_a_115_, 1);
v_data_118_ = lean_ctor_get(v_a_115_, 2);
v_sccs_119_ = lean_ctor_get(v_a_115_, 3);
v_isSharedCheck_197_ = !lean_is_exclusive(v_a_115_);
if (v_isSharedCheck_197_ == 0)
{
v___x_121_ = v_a_115_;
v_isShared_122_ = v_isSharedCheck_197_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_sccs_119_);
lean_inc(v_data_118_);
lean_inc(v_nextIndex_117_);
lean_inc(v_stack_116_);
lean_dec(v_a_115_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_197_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___y_125_; lean_object* v___x_130_; 
v___x_123_ = lean_box(0);
lean_inc(v_a_113_);
lean_inc_ref(v_inst_112_);
lean_inc_ref(v_inst_111_);
v___x_130_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_111_, v_inst_112_, v_data_118_, v_a_113_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_dec_ref(v_f_114_);
lean_dec(v_a_113_);
lean_dec_ref(v_inst_112_);
lean_dec_ref(v_inst_111_);
v___y_125_ = v_data_118_;
goto v___jp_124_;
}
else
{
lean_object* v_val_131_; lean_object* v___x_132_; lean_object* v___y_134_; lean_object* v_i_135_; lean_object* v___y_141_; lean_object* v___y_151_; lean_object* v_i_152_; lean_object* v___x_167_; 
v_val_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_val_131_);
lean_dec_ref_known(v___x_130_, 1);
v___x_132_ = lean_apply_1(v_f_114_, v_val_131_);
lean_inc(v_a_113_);
lean_inc_ref(v_inst_112_);
lean_inc_ref(v_inst_111_);
v___x_167_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_111_, v_inst_112_, v_data_118_, v_a_113_);
switch(lean_obj_tag(v___x_167_))
{
case 0:
{
lean_object* v_index_168_; lean_object* v_size_169_; lean_object* v___x_170_; 
lean_dec_ref(v_inst_112_);
lean_dec_ref(v_inst_111_);
v_index_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_index_168_);
lean_dec_ref_known(v___x_167_, 3);
v_size_169_ = lean_ctor_get(v_data_118_, 0);
lean_inc(v_size_169_);
v___x_170_ = l_Std_DHashMap_Raw_setEntry___redArg(v_data_118_, v_size_169_, v_index_168_, v_a_113_, v___x_132_);
lean_dec(v_index_168_);
v___y_125_ = v___x_170_;
goto v___jp_124_;
}
case 1:
{
lean_object* v_index_171_; lean_object* v_size_172_; lean_object* v_keyArray_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v_index_171_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_index_171_);
lean_dec_ref_known(v___x_167_, 1);
v_size_172_ = lean_ctor_get(v_data_118_, 0);
v_keyArray_173_ = lean_ctor_get(v_data_118_, 1);
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_nat_add(v_size_172_, v___x_174_);
v___x_176_ = lean_array_get_size(v_keyArray_173_);
v___x_177_ = lean_nat_dec_lt(v___x_175_, v___x_176_);
if (v___x_177_ == 0)
{
lean_dec(v___x_175_);
lean_dec(v_index_171_);
goto v___jp_157_;
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_178_ = lean_unsigned_to_nat(4u);
v___x_179_ = lean_nat_mul(v___x_175_, v___x_178_);
v___x_180_ = lean_unsigned_to_nat(3u);
v___x_181_ = lean_nat_mul(v___x_176_, v___x_180_);
v___x_182_ = lean_nat_dec_le(v___x_179_, v___x_181_);
lean_dec(v___x_181_);
lean_dec(v___x_179_);
if (v___x_182_ == 0)
{
lean_dec(v___x_175_);
lean_dec(v_index_171_);
goto v___jp_157_;
}
else
{
lean_object* v___x_183_; 
lean_dec_ref(v_inst_112_);
lean_dec_ref(v_inst_111_);
v___x_183_ = l_Std_DHashMap_Raw_setEntry___redArg(v_data_118_, v___x_175_, v_index_171_, v_a_113_, v___x_132_);
lean_dec(v_index_171_);
v___y_125_ = v___x_183_;
goto v___jp_124_;
}
}
}
default: 
{
lean_object* v_size_184_; lean_object* v_keyArray_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v_size_184_ = lean_ctor_get(v_data_118_, 0);
v_keyArray_185_ = lean_ctor_get(v_data_118_, 1);
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_add(v_size_184_, v___x_186_);
v___x_188_ = lean_array_get_size(v_keyArray_185_);
v___x_189_ = lean_nat_dec_lt(v___x_187_, v___x_188_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; 
lean_dec(v___x_187_);
lean_inc_ref(v_inst_112_);
lean_inc_ref(v_inst_111_);
v___x_190_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_111_, v_inst_112_, v_data_118_);
v___y_141_ = v___x_190_;
goto v___jp_140_;
}
else
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_191_ = lean_unsigned_to_nat(4u);
v___x_192_ = lean_nat_mul(v___x_187_, v___x_191_);
lean_dec(v___x_187_);
v___x_193_ = lean_unsigned_to_nat(3u);
v___x_194_ = lean_nat_mul(v___x_188_, v___x_193_);
v___x_195_ = lean_nat_dec_le(v___x_192_, v___x_194_);
lean_dec(v___x_194_);
lean_dec(v___x_192_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; 
lean_inc_ref(v_inst_112_);
lean_inc_ref(v_inst_111_);
v___x_196_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_111_, v_inst_112_, v_data_118_);
v___y_141_ = v___x_196_;
goto v___jp_140_;
}
else
{
v___y_141_ = v_data_118_;
goto v___jp_140_;
}
}
}
}
v___jp_133_:
{
lean_object* v_size_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_size_136_ = lean_ctor_get(v___y_134_, 0);
v___x_137_ = lean_unsigned_to_nat(1u);
v___x_138_ = lean_nat_add(v_size_136_, v___x_137_);
v___x_139_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_134_, v___x_138_, v_i_135_, v_a_113_, v___x_132_);
lean_dec(v_i_135_);
v___y_125_ = v___x_139_;
goto v___jp_124_;
}
v___jp_140_:
{
lean_object* v___x_142_; 
lean_inc(v_a_113_);
v___x_142_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_111_, v_inst_112_, v___y_141_, v_a_113_);
switch(lean_obj_tag(v___x_142_))
{
case 0:
{
lean_object* v_index_143_; lean_object* v_size_144_; lean_object* v___x_145_; 
v_index_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_index_143_);
lean_dec_ref_known(v___x_142_, 3);
v_size_144_ = lean_ctor_get(v___y_141_, 0);
lean_inc(v_size_144_);
v___x_145_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_141_, v_size_144_, v_index_143_, v_a_113_, v___x_132_);
lean_dec(v_index_143_);
v___y_125_ = v___x_145_;
goto v___jp_124_;
}
case 1:
{
lean_object* v_index_146_; 
v_index_146_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_index_146_);
lean_dec_ref_known(v___x_142_, 1);
v___y_134_ = v___y_141_;
v_i_135_ = v_index_146_;
goto v___jp_133_;
}
default: 
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_141_, v___x_147_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_index_149_; 
v_index_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_index_149_);
lean_dec_ref_known(v___x_148_, 1);
v___y_134_ = v___y_141_;
v_i_135_ = v_index_149_;
goto v___jp_133_;
}
else
{
lean_dec_ref(v___x_132_);
lean_dec(v_a_113_);
v___y_125_ = v___y_141_;
goto v___jp_124_;
}
}
}
}
v___jp_150_:
{
lean_object* v_size_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_size_153_ = lean_ctor_get(v___y_151_, 0);
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_nat_add(v_size_153_, v___x_154_);
v___x_156_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_151_, v___x_155_, v_i_152_, v_a_113_, v___x_132_);
lean_dec(v_i_152_);
v___y_125_ = v___x_156_;
goto v___jp_124_;
}
v___jp_157_:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
lean_inc_ref(v_inst_112_);
lean_inc_ref(v_inst_111_);
v___x_158_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_111_, v_inst_112_, v_data_118_);
lean_inc(v_a_113_);
v___x_159_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_111_, v_inst_112_, v___x_158_, v_a_113_);
switch(lean_obj_tag(v___x_159_))
{
case 0:
{
lean_object* v_index_160_; lean_object* v_size_161_; lean_object* v___x_162_; 
v_index_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_index_160_);
lean_dec_ref_known(v___x_159_, 3);
v_size_161_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_size_161_);
v___x_162_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_158_, v_size_161_, v_index_160_, v_a_113_, v___x_132_);
lean_dec(v_index_160_);
v___y_125_ = v___x_162_;
goto v___jp_124_;
}
case 1:
{
lean_object* v_index_163_; 
v_index_163_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_index_163_);
lean_dec_ref_known(v___x_159_, 1);
v___y_151_ = v___x_158_;
v_i_152_ = v_index_163_;
goto v___jp_150_;
}
default: 
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_158_, v___x_164_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_index_166_; 
v_index_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_index_166_);
lean_dec_ref_known(v___x_165_, 1);
v___y_151_ = v___x_158_;
v_i_152_ = v_index_166_;
goto v___jp_150_;
}
else
{
lean_dec_ref(v___x_132_);
lean_dec(v_a_113_);
v___y_125_ = v___x_158_;
goto v___jp_124_;
}
}
}
}
}
v___jp_124_:
{
lean_object* v___x_127_; 
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 2, v___y_125_);
v___x_127_ = v___x_121_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_stack_116_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_nextIndex_117_);
lean_ctor_set(v_reuseFailAlloc_129_, 2, v___y_125_);
lean_ctor_set(v_reuseFailAlloc_129_, 3, v_sccs_119_);
v___x_127_ = v_reuseFailAlloc_129_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_128_; 
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_123_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
return v___x_128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf(lean_object* v_00_u03b1_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_a_201_, lean_object* v_f_202_, lean_object* v_a_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___redArg(v_inst_199_, v_inst_200_, v_a_201_, v_f_202_, v_a_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg___lam__0(lean_object* v_d_205_){
_start:
{
lean_object* v_index_x3f_206_; lean_object* v_lowlink_x3f_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_215_; 
v_index_x3f_206_ = lean_ctor_get(v_d_205_, 0);
v_lowlink_x3f_207_ = lean_ctor_get(v_d_205_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v_d_205_);
if (v_isSharedCheck_215_ == 0)
{
v___x_209_ = v_d_205_;
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_lowlink_x3f_207_);
lean_inc(v_index_x3f_206_);
lean_dec(v_d_205_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
uint8_t v___x_211_; lean_object* v___x_213_; 
v___x_211_ = 0;
if (v_isShared_210_ == 0)
{
v___x_213_ = v___x_209_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_index_x3f_206_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_lowlink_x3f_207_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_ctor_set_uint8(v___x_213_, sizeof(void*)*2, v___x_211_);
return v___x_213_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg(lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v___f_221_; lean_object* v___x_222_; 
v___f_221_ = ((lean_object*)(l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg___closed__0));
v___x_222_ = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___redArg(v_inst_217_, v_inst_218_, v_a_219_, v___f_221_, v_a_220_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack(lean_object* v_00_u03b1_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg(v_inst_224_, v_inst_225_, v_a_226_, v_a_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___redArg___lam__0(lean_object* v_v_229_, lean_object* v_d_230_){
_start:
{
if (lean_obj_tag(v_v_229_) == 0)
{
return v_d_230_;
}
else
{
lean_object* v_lowlink_x3f_231_; 
v_lowlink_x3f_231_ = lean_ctor_get(v_d_230_, 1);
if (lean_obj_tag(v_lowlink_x3f_231_) == 0)
{
lean_object* v_index_x3f_232_; uint8_t v_onStack_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
v_index_x3f_232_ = lean_ctor_get(v_d_230_, 0);
v_onStack_233_ = lean_ctor_get_uint8(v_d_230_, sizeof(void*)*2);
v_isSharedCheck_240_ = !lean_is_exclusive(v_d_230_);
if (v_isSharedCheck_240_ == 0)
{
lean_object* v_unused_241_; 
v_unused_241_ = lean_ctor_get(v_d_230_, 1);
lean_dec(v_unused_241_);
v___x_235_ = v_d_230_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_index_x3f_232_);
lean_dec(v_d_230_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v_v_229_);
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_index_x3f_232_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_v_229_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, sizeof(void*)*2, v_onStack_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
else
{
lean_object* v_index_x3f_242_; uint8_t v_onStack_243_; lean_object* v_val_244_; lean_object* v_val_245_; uint8_t v___x_246_; 
v_index_x3f_242_ = lean_ctor_get(v_d_230_, 0);
v_onStack_243_ = lean_ctor_get_uint8(v_d_230_, sizeof(void*)*2);
v_val_244_ = lean_ctor_get(v_v_229_, 0);
v_val_245_ = lean_ctor_get(v_lowlink_x3f_231_, 0);
v___x_246_ = lean_nat_dec_lt(v_val_245_, v_val_244_);
if (v___x_246_ == 0)
{
lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_inc(v_index_x3f_242_);
v_isSharedCheck_253_ = !lean_is_exclusive(v_d_230_);
if (v_isSharedCheck_253_ == 0)
{
lean_object* v_unused_254_; lean_object* v_unused_255_; 
v_unused_254_ = lean_ctor_get(v_d_230_, 1);
lean_dec(v_unused_254_);
v_unused_255_ = lean_ctor_get(v_d_230_, 0);
lean_dec(v_unused_255_);
v___x_248_ = v_d_230_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_dec(v_d_230_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 1, v_v_229_);
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_index_x3f_242_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_v_229_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, sizeof(void*)*2, v_onStack_243_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
else
{
lean_dec_ref_known(v_v_229_, 1);
return v_d_230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___redArg(lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_a_258_, lean_object* v_v_259_, lean_object* v_a_260_){
_start:
{
lean_object* v___f_261_; lean_object* v___x_262_; 
v___f_261_ = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___redArg___lam__0), 2, 1);
lean_closure_set(v___f_261_, 0, v_v_259_);
v___x_262_ = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___redArg(v_inst_256_, v_inst_257_, v_a_258_, v___f_261_, v_a_260_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf(lean_object* v_00_u03b1_263_, lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_a_266_, lean_object* v_v_267_, lean_object* v_a_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___redArg(v_inst_264_, v_inst_265_, v_a_266_, v_v_267_, v_a_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___redArg(lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_a_272_, lean_object* v_x_273_, lean_object* v_x_274_, lean_object* v_a_275_){
_start:
{
if (lean_obj_tag(v_x_273_) == 0)
{
lean_object* v_nextIndex_276_; lean_object* v_data_277_; lean_object* v_sccs_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_288_; 
lean_dec(v_a_272_);
lean_dec_ref(v_inst_271_);
lean_dec_ref(v_inst_270_);
v_nextIndex_276_ = lean_ctor_get(v_a_275_, 1);
v_data_277_ = lean_ctor_get(v_a_275_, 2);
v_sccs_278_ = lean_ctor_get(v_a_275_, 3);
v_isSharedCheck_288_ = !lean_is_exclusive(v_a_275_);
if (v_isSharedCheck_288_ == 0)
{
lean_object* v_unused_289_; 
v_unused_289_ = lean_ctor_get(v_a_275_, 0);
lean_dec(v_unused_289_);
v___x_280_ = v_a_275_;
v_isShared_281_ = v_isSharedCheck_288_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_sccs_278_);
lean_inc(v_data_277_);
lean_inc(v_nextIndex_276_);
lean_dec(v_a_275_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_288_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_282_ = lean_box(0);
v___x_283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_283_, 0, v_x_274_);
lean_ctor_set(v___x_283_, 1, v_sccs_278_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 3, v___x_283_);
lean_ctor_set(v___x_280_, 0, v_x_273_);
v___x_285_ = v___x_280_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_x_273_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_nextIndex_276_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v_data_277_);
lean_ctor_set(v_reuseFailAlloc_287_, 3, v___x_283_);
v___x_285_ = v_reuseFailAlloc_287_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_286_; 
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_282_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
return v___x_286_;
}
}
}
else
{
lean_object* v_head_290_; lean_object* v_tail_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_324_; 
v_head_290_ = lean_ctor_get(v_x_273_, 0);
v_tail_291_ = lean_ctor_get(v_x_273_, 1);
v_isSharedCheck_324_ = !lean_is_exclusive(v_x_273_);
if (v_isSharedCheck_324_ == 0)
{
v___x_293_ = v_x_273_;
v_isShared_294_ = v_isSharedCheck_324_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_tail_291_);
lean_inc(v_head_290_);
lean_dec(v_x_273_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_324_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v_snd_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_322_; 
lean_inc(v_head_290_);
lean_inc_ref(v_inst_271_);
lean_inc_ref(v_inst_270_);
v___x_295_ = l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg(v_inst_270_, v_inst_271_, v_head_290_, v_a_275_);
v_snd_296_ = lean_ctor_get(v___x_295_, 1);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_322_ == 0)
{
lean_object* v_unused_323_; 
v_unused_323_ = lean_ctor_get(v___x_295_, 0);
lean_dec(v_unused_323_);
v___x_298_ = v___x_295_;
v_isShared_299_ = v_isSharedCheck_322_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_snd_296_);
lean_dec(v___x_295_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_322_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
lean_inc(v_head_290_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v_x_274_);
v___x_301_ = v___x_293_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_head_290_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_x_274_);
v___x_301_ = v_reuseFailAlloc_321_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; uint8_t v___x_303_; 
lean_inc_ref(v_inst_270_);
lean_inc(v_a_272_);
v___x_302_ = lean_apply_2(v_inst_270_, v_a_272_, v_head_290_);
v___x_303_ = lean_unbox(v___x_302_);
if (v___x_303_ == 0)
{
lean_del_object(v___x_298_);
v_x_273_ = v_tail_291_;
v_x_274_ = v___x_301_;
v_a_275_ = v_snd_296_;
goto _start;
}
else
{
lean_object* v_nextIndex_305_; lean_object* v_data_306_; lean_object* v_sccs_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_319_; 
lean_dec(v_a_272_);
lean_dec_ref(v_inst_271_);
lean_dec_ref(v_inst_270_);
v_nextIndex_305_ = lean_ctor_get(v_snd_296_, 1);
v_data_306_ = lean_ctor_get(v_snd_296_, 2);
v_sccs_307_ = lean_ctor_get(v_snd_296_, 3);
v_isSharedCheck_319_ = !lean_is_exclusive(v_snd_296_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; 
v_unused_320_ = lean_ctor_get(v_snd_296_, 0);
lean_dec(v_unused_320_);
v___x_309_ = v_snd_296_;
v_isShared_310_ = v_isSharedCheck_319_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_sccs_307_);
lean_inc(v_data_306_);
lean_inc(v_nextIndex_305_);
lean_dec(v_snd_296_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_319_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_311_ = lean_box(0);
v___x_312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_301_);
lean_ctor_set(v___x_312_, 1, v_sccs_307_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 3, v___x_312_);
lean_ctor_set(v___x_309_, 0, v_tail_291_);
v___x_314_ = v___x_309_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_tail_291_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_nextIndex_305_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v_data_306_);
lean_ctor_set(v_reuseFailAlloc_318_, 3, v___x_312_);
v___x_314_ = v_reuseFailAlloc_318_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_316_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 1, v___x_314_);
lean_ctor_set(v___x_298_, 0, v___x_311_);
v___x_316_ = v___x_298_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add(lean_object* v_00_u03b1_325_, lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_a_328_, lean_object* v_x_329_, lean_object* v_x_330_, lean_object* v_a_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___redArg(v_inst_326_, v_inst_327_, v_a_328_, v_x_329_, v_x_330_, v_a_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___redArg(lean_object* v_inst_333_, lean_object* v_inst_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_stack_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_stack_337_ = lean_ctor_get(v_a_336_, 0);
lean_inc(v_stack_337_);
v___x_338_ = lean_box(0);
v___x_339_ = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___redArg(v_inst_333_, v_inst_334_, v_a_335_, v_stack_337_, v___x_338_, v_a_336_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC(lean_object* v_00_u03b1_340_, lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___redArg(v_inst_341_, v_inst_342_, v_a_343_, v_a_344_);
return v___x_345_;
}
}
static lean_object* _init_l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__20(void){
_start:
{
lean_object* v___x_391_; lean_object* v___f_392_; 
v___x_391_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_392_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_392_, 0, v___x_391_);
return v___f_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg(lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_successorsOf_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v_snd_400_; lean_object* v___f_401_; lean_object* v___x_402_; lean_object* v___x_1010__overap_403_; lean_object* v___x_404_; lean_object* v_snd_405_; lean_object* v___x_406_; lean_object* v_fst_407_; lean_object* v_snd_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_421_; 
v___x_398_ = ((lean_object*)(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__19));
lean_inc_n(v_a_396_, 4);
lean_inc_ref_n(v_inst_394_, 3);
lean_inc_ref_n(v_inst_393_, 3);
v___x_399_ = l___private_Lean_Util_SCC_0__Lean_SCC_push___redArg(v_inst_393_, v_inst_394_, v_a_396_, v_a_397_);
v_snd_400_ = lean_ctor_get(v___x_399_, 1);
lean_inc(v_snd_400_);
lean_dec_ref(v___x_399_);
lean_inc_ref(v_successorsOf_395_);
v___f_401_ = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___lam__0), 6, 4);
lean_closure_set(v___f_401_, 0, v_inst_393_);
lean_closure_set(v___f_401_, 1, v_inst_394_);
lean_closure_set(v___f_401_, 2, v_successorsOf_395_);
lean_closure_set(v___f_401_, 3, v_a_396_);
v___x_402_ = lean_apply_1(v_successorsOf_395_, v_a_396_);
v___x_1010__overap_403_ = l_List_forM___redArg(v___x_398_, v___x_402_, v___f_401_);
v___x_404_ = lean_apply_1(v___x_1010__overap_403_, v_snd_400_);
v_snd_405_ = lean_ctor_get(v___x_404_, 1);
lean_inc(v_snd_405_);
lean_dec_ref(v___x_404_);
v___x_406_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg(v_inst_393_, v_inst_394_, v_a_396_, v_snd_405_);
v_fst_407_ = lean_ctor_get(v___x_406_, 0);
v_snd_408_ = lean_ctor_get(v___x_406_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_421_ == 0)
{
v___x_410_ = v___x_406_;
v_isShared_411_ = v_isSharedCheck_421_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_snd_408_);
lean_inc(v_fst_407_);
lean_dec(v___x_406_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_421_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v_index_x3f_412_; lean_object* v_lowlink_x3f_413_; lean_object* v___f_414_; uint8_t v___x_415_; 
v_index_x3f_412_ = lean_ctor_get(v_fst_407_, 0);
lean_inc(v_index_x3f_412_);
v_lowlink_x3f_413_ = lean_ctor_get(v_fst_407_, 1);
lean_inc(v_lowlink_x3f_413_);
lean_dec(v_fst_407_);
v___f_414_ = lean_obj_once(&l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__20, &l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__20_once, _init_l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__20);
v___x_415_ = l_Option_instBEq_beq___redArg(v___f_414_, v_lowlink_x3f_413_, v_index_x3f_412_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_418_; 
lean_dec(v_a_396_);
lean_dec_ref(v_inst_394_);
lean_dec_ref(v_inst_393_);
v___x_416_ = lean_box(0);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_416_);
v___x_418_ = v___x_410_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_snd_408_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
else
{
lean_object* v___x_420_; 
lean_del_object(v___x_410_);
v___x_420_ = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___redArg(v_inst_393_, v_inst_394_, v_a_396_, v_snd_408_);
return v___x_420_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___lam__0(lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_successorsOf_424_, lean_object* v_a_425_, lean_object* v_b_426_, lean_object* v___y_427_){
_start:
{
lean_object* v___x_428_; lean_object* v_fst_429_; lean_object* v_index_x3f_430_; 
lean_inc(v_b_426_);
lean_inc_ref(v_inst_423_);
lean_inc_ref(v_inst_422_);
v___x_428_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg(v_inst_422_, v_inst_423_, v_b_426_, v___y_427_);
v_fst_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_fst_429_);
v_index_x3f_430_ = lean_ctor_get(v_fst_429_, 0);
lean_inc(v_index_x3f_430_);
if (lean_obj_tag(v_index_x3f_430_) == 0)
{
lean_object* v_snd_431_; lean_object* v___x_432_; lean_object* v_snd_433_; lean_object* v___x_434_; lean_object* v_fst_435_; lean_object* v_snd_436_; lean_object* v_lowlink_x3f_437_; lean_object* v___x_438_; 
lean_dec(v_fst_429_);
v_snd_431_ = lean_ctor_get(v___x_428_, 1);
lean_inc(v_snd_431_);
lean_dec_ref(v___x_428_);
lean_inc(v_b_426_);
lean_inc_ref_n(v_inst_423_, 2);
lean_inc_ref_n(v_inst_422_, 2);
v___x_432_ = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg(v_inst_422_, v_inst_423_, v_successorsOf_424_, v_b_426_, v_snd_431_);
v_snd_433_ = lean_ctor_get(v___x_432_, 1);
lean_inc(v_snd_433_);
lean_dec_ref(v___x_432_);
v___x_434_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg(v_inst_422_, v_inst_423_, v_b_426_, v_snd_433_);
v_fst_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_fst_435_);
v_snd_436_ = lean_ctor_get(v___x_434_, 1);
lean_inc(v_snd_436_);
lean_dec_ref(v___x_434_);
v_lowlink_x3f_437_ = lean_ctor_get(v_fst_435_, 1);
lean_inc(v_lowlink_x3f_437_);
lean_dec(v_fst_435_);
v___x_438_ = l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___redArg(v_inst_422_, v_inst_423_, v_a_425_, v_lowlink_x3f_437_, v_snd_436_);
return v___x_438_;
}
else
{
uint8_t v_onStack_439_; 
lean_dec(v_b_426_);
lean_dec_ref(v_successorsOf_424_);
v_onStack_439_ = lean_ctor_get_uint8(v_fst_429_, sizeof(void*)*2);
lean_dec(v_fst_429_);
if (v_onStack_439_ == 0)
{
lean_object* v_snd_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_448_; 
lean_dec_ref_known(v_index_x3f_430_, 1);
lean_dec(v_a_425_);
lean_dec_ref(v_inst_423_);
lean_dec_ref(v_inst_422_);
v_snd_440_ = lean_ctor_get(v___x_428_, 1);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; 
v_unused_449_ = lean_ctor_get(v___x_428_, 0);
lean_dec(v_unused_449_);
v___x_442_ = v___x_428_;
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_snd_440_);
lean_dec(v___x_428_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = lean_box(0);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_444_);
v___x_446_ = v___x_442_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_snd_440_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
else
{
lean_object* v_snd_450_; lean_object* v___x_451_; 
v_snd_450_ = lean_ctor_get(v___x_428_, 1);
lean_inc(v_snd_450_);
lean_dec_ref(v___x_428_);
v___x_451_ = l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___redArg(v_inst_422_, v_inst_423_, v_a_425_, v_index_x3f_430_, v_snd_450_);
return v___x_451_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux(lean_object* v_00_u03b1_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_successorsOf_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg(v_inst_453_, v_inst_454_, v_successorsOf_455_, v_a_456_, v_a_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_SCC_scc___redArg___lam__0(lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_successorsOf_461_, lean_object* v_a_462_, lean_object* v___y_463_){
_start:
{
lean_object* v___x_464_; lean_object* v_fst_465_; lean_object* v_index_x3f_466_; 
lean_inc(v_a_462_);
lean_inc_ref(v_inst_460_);
lean_inc_ref(v_inst_459_);
v___x_464_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg(v_inst_459_, v_inst_460_, v_a_462_, v___y_463_);
v_fst_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_fst_465_);
v_index_x3f_466_ = lean_ctor_get(v_fst_465_, 0);
lean_inc(v_index_x3f_466_);
lean_dec(v_fst_465_);
if (lean_obj_tag(v_index_x3f_466_) == 0)
{
lean_object* v_snd_467_; lean_object* v___x_468_; 
v_snd_467_ = lean_ctor_get(v___x_464_, 1);
lean_inc(v_snd_467_);
lean_dec_ref(v___x_464_);
v___x_468_ = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg(v_inst_459_, v_inst_460_, v_successorsOf_461_, v_a_462_, v_snd_467_);
return v___x_468_;
}
else
{
lean_object* v_snd_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_477_; 
lean_dec_ref_known(v_index_x3f_466_, 1);
lean_dec(v_a_462_);
lean_dec_ref(v_successorsOf_461_);
lean_dec_ref(v_inst_460_);
lean_dec_ref(v_inst_459_);
v_snd_469_ = lean_ctor_get(v___x_464_, 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_477_ == 0)
{
lean_object* v_unused_478_; 
v_unused_478_ = lean_ctor_get(v___x_464_, 0);
lean_dec(v_unused_478_);
v___x_471_ = v___x_464_;
v_isShared_472_ = v_isSharedCheck_477_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_snd_469_);
lean_dec(v___x_464_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_477_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_473_ = lean_box(0);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_473_);
v___x_475_ = v___x_471_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_snd_469_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
static lean_object* _init_l_Lean_SCC_scc___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_479_; lean_object* v___x_480_; 
v_cellCount_479_ = lean_unsigned_to_nat(16u);
v___x_480_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_479_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_SCC_scc___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_481_; lean_object* v___x_482_; 
v_cellCount_481_ = lean_unsigned_to_nat(16u);
v___x_482_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_481_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_SCC_scc___redArg___closed__2(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_483_ = lean_obj_once(&l_Lean_SCC_scc___redArg___closed__1, &l_Lean_SCC_scc___redArg___closed__1_once, _init_l_Lean_SCC_scc___redArg___closed__1);
v___x_484_ = lean_obj_once(&l_Lean_SCC_scc___redArg___closed__0, &l_Lean_SCC_scc___redArg___closed__0_once, _init_l_Lean_SCC_scc___redArg___closed__0);
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___x_484_);
lean_ctor_set(v___x_486_, 2, v___x_483_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_SCC_scc___redArg___closed__3(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_487_ = lean_obj_once(&l_Lean_SCC_scc___redArg___closed__2, &l_Lean_SCC_scc___redArg___closed__2_once, _init_l_Lean_SCC_scc___redArg___closed__2);
v___x_488_ = lean_unsigned_to_nat(0u);
v___x_489_ = lean_box(0);
v___x_490_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v___x_488_);
lean_ctor_set(v___x_490_, 2, v___x_487_);
lean_ctor_set(v___x_490_, 3, v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_SCC_scc___redArg(lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_vertices_493_, lean_object* v_successorsOf_494_){
_start:
{
lean_object* v___f_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_384__overap_498_; lean_object* v___x_499_; lean_object* v_snd_500_; lean_object* v_sccs_501_; lean_object* v___x_502_; 
v___f_495_ = lean_alloc_closure((void*)(l_Lean_SCC_scc___redArg___lam__0), 5, 3);
lean_closure_set(v___f_495_, 0, v_inst_491_);
lean_closure_set(v___f_495_, 1, v_inst_492_);
lean_closure_set(v___f_495_, 2, v_successorsOf_494_);
v___x_496_ = ((lean_object*)(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__19));
v___x_497_ = lean_obj_once(&l_Lean_SCC_scc___redArg___closed__3, &l_Lean_SCC_scc___redArg___closed__3_once, _init_l_Lean_SCC_scc___redArg___closed__3);
v___x_384__overap_498_ = l_List_forM___redArg(v___x_496_, v_vertices_493_, v___f_495_);
v___x_499_ = lean_apply_1(v___x_384__overap_498_, v___x_497_);
v_snd_500_ = lean_ctor_get(v___x_499_, 1);
lean_inc(v_snd_500_);
lean_dec_ref(v___x_499_);
v_sccs_501_ = lean_ctor_get(v_snd_500_, 3);
lean_inc(v_sccs_501_);
lean_dec(v_snd_500_);
v___x_502_ = l_List_reverse___redArg(v_sccs_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_SCC_scc(lean_object* v_00_u03b1_503_, lean_object* v_inst_504_, lean_object* v_inst_505_, lean_object* v_vertices_506_, lean_object* v_successorsOf_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_SCC_scc___redArg(v_inst_504_, v_inst_505_, v_vertices_506_, v_successorsOf_507_);
return v___x_508_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_SCC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
