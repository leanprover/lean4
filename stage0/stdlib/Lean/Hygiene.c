// Lean compiler output
// Module: Lean.Hygiene
// Imports: public import Lean.Data.Format
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
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
uint8_t l_Std_Format_getUnicode(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_toSuperscriptString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotation___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotation___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotation___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotation___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotation___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotation___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotation___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotation___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Unhygienic_instMonadQuotation___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__0 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__0_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Unhygienic_instMonadQuotation___lam__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__1 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__1_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Unhygienic_instMonadQuotation___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__2 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__2_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Unhygienic_instMonadQuotation___lam__3___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__3 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__3_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__4 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__4_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__5 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__5_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__6 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__6_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__7 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__7_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__8 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__8_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__9 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__9_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__10 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__10_value;
static const lean_ctor_object l_Lean_Unhygienic_instMonadQuotation___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__4_value),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__5_value)}};
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__11 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__11_value;
static const lean_ctor_object l_Lean_Unhygienic_instMonadQuotation___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__11_value),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__6_value),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__7_value),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__8_value),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__9_value)}};
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__12 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__12_value;
static const lean_ctor_object l_Lean_Unhygienic_instMonadQuotation___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__12_value),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__10_value)}};
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__13 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__13_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__13_value)} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__14 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__14_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__4, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__13_value)} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__15 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__15_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__7, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__13_value)} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__16 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__16_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__9, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__13_value)} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__17 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__17_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_map, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__13_value)} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__18 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__18_value;
static const lean_ctor_object l_Lean_Unhygienic_instMonadQuotation___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__18_value),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__14_value)}};
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__19 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__19_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_pure, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__13_value)} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__20 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__20_value;
static const lean_ctor_object l_Lean_Unhygienic_instMonadQuotation___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__19_value),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__20_value),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__15_value),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__16_value),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__17_value)}};
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__21 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__21_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_bind, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__13_value)} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__22 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__22_value;
static const lean_ctor_object l_Lean_Unhygienic_instMonadQuotation___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__21_value),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__22_value)}};
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__23 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__23_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_read___boxed, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__23_value)} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__24 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__24_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_bind___boxed, .m_arity = 8, .m_num_fixed = 7, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__24_value),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__0_value)} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__25 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__25_value;
static const lean_ctor_object l_Lean_Unhygienic_instMonadQuotation___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__25_value),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__1_value)}};
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__26 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__26_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_bind___boxed, .m_arity = 8, .m_num_fixed = 7, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__24_value),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__2_value)} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__27 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__27_value;
static const lean_string_object l_Lean_Unhygienic_instMonadQuotation___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "UnhygienicMain"};
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__28 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__28_value;
static const lean_ctor_object l_Lean_Unhygienic_instMonadQuotation___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__28_value),LEAN_SCALAR_PTR_LITERAL(124, 169, 242, 144, 140, 56, 85, 78)}};
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__29 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__29_value;
static const lean_closure_object l_Lean_Unhygienic_instMonadQuotation___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_pure___boxed, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__29_value)} };
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__30 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__30_value;
static const lean_ctor_object l_Lean_Unhygienic_instMonadQuotation___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__26_value),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__27_value),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__30_value),((lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__3_value)}};
static const lean_object* l_Lean_Unhygienic_instMonadQuotation___closed__31 = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__31_value;
LEAN_EXPORT const lean_object* l_Lean_Unhygienic_instMonadQuotation = (const lean_object*)&l_Lean_Unhygienic_instMonadQuotation___closed__31_value;
static lean_once_cell_t l_Lean_Unhygienic_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Unhygienic_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Unhygienic_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Unhygienic_run___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Unhygienic_run___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Unhygienic_run(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "_inaccessible"};
static const lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__0 = (const lean_object*)&l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__0_value;
static const lean_ctor_object l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 29, 104, 7, 111, 207, 123, 40)}};
static const lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__1 = (const lean_object*)&l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__1_value;
static const lean_string_object l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "✝"};
static const lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__2 = (const lean_object*)&l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⁻"};
static const lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___closed__0 = (const lean_object*)&l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "sanitizeNames"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(147, 143, 157, 1, 169, 13, 114, 103)}};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__3_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "add suffix to shadowed/inaccessible variables when pretty printing"};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__5_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(72, 7, 204, 203, 213, 214, 129, 229)}};
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(110, 75, 30, 190, 199, 100, 219, 176)}};
static const lean_object* l_Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_sanitizeNames;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_getSanitizeNames_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_getSanitizeNames_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getSanitizeNames(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getSanitizeNames___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkFreshInaccessibleUserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_sanitizeName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux_spec__0(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_sanitizeSyntax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotation___lam__0(lean_object* v_____do__lift_1_, lean_object* v___y_2_, lean_object* v___y_3_){
_start:
{
lean_object* v_ref_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_11_; 
v_ref_4_ = lean_ctor_get(v_____do__lift_1_, 0);
v_isSharedCheck_11_ = !lean_is_exclusive(v_____do__lift_1_);
if (v_isSharedCheck_11_ == 0)
{
lean_object* v_unused_12_; 
v_unused_12_ = lean_ctor_get(v_____do__lift_1_, 1);
lean_dec(v_unused_12_);
v___x_6_ = v_____do__lift_1_;
v_isShared_7_ = v_isSharedCheck_11_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_ref_4_);
lean_dec(v_____do__lift_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_11_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v___x_9_; 
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 1, v___y_3_);
v___x_9_ = v___x_6_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_10_; 
v_reuseFailAlloc_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_10_, 0, v_ref_4_);
lean_ctor_set(v_reuseFailAlloc_10_, 1, v___y_3_);
v___x_9_ = v_reuseFailAlloc_10_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotation___lam__0___boxed(lean_object* v_____do__lift_13_, lean_object* v___y_14_, lean_object* v___y_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_Unhygienic_instMonadQuotation___lam__0(v_____do__lift_13_, v___y_14_, v___y_15_);
lean_dec_ref(v___y_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotation___lam__1(lean_object* v_00_u03b1_17_, lean_object* v_ref_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_scope_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_scope_22_ = lean_ctor_get(v___y_20_, 1);
lean_inc(v_scope_22_);
v___x_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_23_, 0, v_ref_18_);
lean_ctor_set(v___x_23_, 1, v_scope_22_);
v___x_24_ = lean_apply_2(v___y_19_, v___x_23_, v___y_21_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotation___lam__1___boxed(lean_object* v_00_u03b1_25_, lean_object* v_ref_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Unhygienic_instMonadQuotation___lam__1(v_00_u03b1_25_, v_ref_26_, v___y_27_, v___y_28_, v___y_29_);
lean_dec_ref(v___y_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotation___lam__2(lean_object* v_____do__lift_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v_scope_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_41_; 
v_scope_34_ = lean_ctor_get(v_____do__lift_31_, 1);
v_isSharedCheck_41_ = !lean_is_exclusive(v_____do__lift_31_);
if (v_isSharedCheck_41_ == 0)
{
lean_object* v_unused_42_; 
v_unused_42_ = lean_ctor_get(v_____do__lift_31_, 0);
lean_dec(v_unused_42_);
v___x_36_ = v_____do__lift_31_;
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_scope_34_);
lean_dec(v_____do__lift_31_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_39_; 
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 1, v___y_33_);
lean_ctor_set(v___x_36_, 0, v_scope_34_);
v___x_39_ = v___x_36_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_scope_34_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v___y_33_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotation___lam__2___boxed(lean_object* v_____do__lift_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Unhygienic_instMonadQuotation___lam__2(v_____do__lift_43_, v___y_44_, v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotation___lam__3(lean_object* v_00_u03b1_47_, lean_object* v_x_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_ref_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v_ref_51_ = lean_ctor_get(v___y_49_, 0);
v___x_52_ = lean_unsigned_to_nat(1u);
v___x_53_ = lean_nat_add(v___y_50_, v___x_52_);
lean_inc(v_ref_51_);
v___x_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_54_, 0, v_ref_51_);
lean_ctor_set(v___x_54_, 1, v___y_50_);
v___x_55_ = lean_apply_2(v_x_48_, v___x_54_, v___x_53_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotation___lam__3___boxed(lean_object* v_00_u03b1_56_, lean_object* v_x_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Unhygienic_instMonadQuotation___lam__3(v_00_u03b1_56_, v_x_57_, v___y_58_, v___y_59_);
lean_dec_ref(v___y_58_);
return v_res_60_;
}
}
static lean_object* _init_l_Lean_Unhygienic_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = l_Lean_firstFrontendMacroScope;
v___x_136_ = lean_box(0);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___x_135_);
return v___x_137_;
}
}
static lean_object* _init_l_Lean_Unhygienic_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = lean_unsigned_to_nat(1u);
v___x_139_ = l_Lean_firstFrontendMacroScope;
v___x_140_ = lean_nat_add(v___x_139_, v___x_138_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Unhygienic_run___redArg(lean_object* v_x_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v_fst_145_; 
v___x_142_ = lean_obj_once(&l_Lean_Unhygienic_run___redArg___closed__0, &l_Lean_Unhygienic_run___redArg___closed__0_once, _init_l_Lean_Unhygienic_run___redArg___closed__0);
v___x_143_ = lean_obj_once(&l_Lean_Unhygienic_run___redArg___closed__1, &l_Lean_Unhygienic_run___redArg___closed__1_once, _init_l_Lean_Unhygienic_run___redArg___closed__1);
v___x_144_ = lean_apply_2(v_x_141_, v___x_142_, v___x_143_);
v_fst_145_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_fst_145_);
lean_dec_ref(v___x_144_);
return v_fst_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Unhygienic_run(lean_object* v_00_u03b1_146_, lean_object* v_x_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v_fst_151_; 
v___x_148_ = lean_obj_once(&l_Lean_Unhygienic_run___redArg___closed__0, &l_Lean_Unhygienic_run___redArg___closed__0_once, _init_l_Lean_Unhygienic_run___redArg___closed__0);
v___x_149_ = lean_obj_once(&l_Lean_Unhygienic_run___redArg___closed__1, &l_Lean_Unhygienic_run___redArg___closed__1_once, _init_l_Lean_Unhygienic_run___redArg___closed__1);
v___x_150_ = lean_apply_2(v_x_147_, v___x_148_, v___x_149_);
v_fst_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_fst_151_);
lean_dec_ref(v___x_150_);
return v_fst_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux(uint8_t v_unicode_156_, lean_object* v_name_157_, lean_object* v_idx_158_){
_start:
{
if (v_unicode_156_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = ((lean_object*)(l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__1));
v___x_160_ = l_Lean_Name_num___override(v___x_159_, v_idx_158_);
v___x_161_ = l_Lean_Name_append(v_name_157_, v___x_160_);
return v___x_161_;
}
else
{
lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_nat_dec_eq(v_idx_158_, v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_164_ = ((lean_object*)(l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__2));
v___x_165_ = l_Nat_toSuperscriptString(v_idx_158_);
v___x_166_ = lean_string_append(v___x_164_, v___x_165_);
lean_dec_ref(v___x_165_);
v___x_167_ = lean_name_append_after(v_name_157_, v___x_166_);
return v___x_167_;
}
else
{
lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec(v_idx_158_);
v___x_168_ = ((lean_object*)(l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__2));
v___x_169_ = lean_name_append_after(v_name_157_, v___x_168_);
return v___x_169_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___boxed(lean_object* v_unicode_170_, lean_object* v_name_171_, lean_object* v_idx_172_){
_start:
{
uint8_t v_unicode_boxed_173_; lean_object* v_res_174_; 
v_unicode_boxed_173_ = lean_unbox(v_unicode_170_);
v_res_174_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux(v_unicode_boxed_173_, v_name_171_, v_idx_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(uint8_t v_unicode_176_, lean_object* v_x_177_){
_start:
{
if (lean_obj_tag(v_x_177_) == 2)
{
lean_object* v_pre_178_; 
v_pre_178_ = lean_ctor_get(v_x_177_, 0);
lean_inc(v_pre_178_);
switch(lean_obj_tag(v_pre_178_))
{
case 1:
{
lean_object* v_i_179_; lean_object* v___x_180_; 
v_i_179_ = lean_ctor_get(v_x_177_, 1);
lean_inc(v_i_179_);
lean_dec_ref(v_x_177_);
v___x_180_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux(v_unicode_176_, v_pre_178_, v_i_179_);
return v___x_180_;
}
case 0:
{
lean_object* v_i_181_; lean_object* v___x_182_; 
v_i_181_ = lean_ctor_get(v_x_177_, 1);
lean_inc(v_i_181_);
lean_dec_ref(v_x_177_);
v___x_182_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux(v_unicode_176_, v_pre_178_, v_i_181_);
return v___x_182_;
}
default: 
{
if (v_unicode_176_ == 0)
{
lean_object* v_i_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_i_183_ = lean_ctor_get(v_x_177_, 1);
lean_inc(v_i_183_);
lean_dec_ref(v_x_177_);
v___x_184_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(v_unicode_176_, v_pre_178_);
v___x_185_ = l_Lean_Name_num___override(v___x_184_, v_i_183_);
return v___x_185_;
}
else
{
lean_object* v_i_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v_i_186_ = lean_ctor_get(v_x_177_, 1);
lean_inc(v_i_186_);
lean_dec_ref(v_x_177_);
v___x_187_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(v_unicode_176_, v_pre_178_);
v___x_188_ = ((lean_object*)(l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___closed__0));
v___x_189_ = l_Nat_toSuperscriptString(v_i_186_);
v___x_190_ = lean_string_append(v___x_188_, v___x_189_);
lean_dec_ref(v___x_189_);
v___x_191_ = lean_name_append_after(v___x_187_, v___x_190_);
return v___x_191_;
}
}
}
}
else
{
return v_x_177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___boxed(lean_object* v_unicode_192_, lean_object* v_x_193_){
_start:
{
uint8_t v_unicode_boxed_194_; lean_object* v_res_195_; 
v_unicode_boxed_194_ = lean_unbox(v_unicode_192_);
v_res_195_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(v_unicode_boxed_194_, v_x_193_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__spec__0(lean_object* v_name_196_, lean_object* v_decl_197_, lean_object* v_ref_198_){
_start:
{
lean_object* v_defValue_200_; lean_object* v_descr_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_228_; 
v_defValue_200_ = lean_ctor_get(v_decl_197_, 0);
v_descr_201_ = lean_ctor_get(v_decl_197_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v_decl_197_);
if (v_isSharedCheck_228_ == 0)
{
v___x_203_ = v_decl_197_;
v_isShared_204_ = v_isSharedCheck_228_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_descr_201_);
lean_inc(v_defValue_200_);
lean_dec(v_decl_197_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_228_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; uint8_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_205_ = lean_alloc_ctor(1, 0, 1);
v___x_206_ = lean_unbox(v_defValue_200_);
lean_ctor_set_uint8(v___x_205_, 0, v___x_206_);
lean_inc_n(v_name_196_, 2);
v___x_207_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_207_, 0, v_name_196_);
lean_ctor_set(v___x_207_, 1, v_ref_198_);
lean_ctor_set(v___x_207_, 2, v___x_205_);
lean_ctor_set(v___x_207_, 3, v_descr_201_);
v___x_208_ = lean_register_option(v_name_196_, v___x_207_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_218_; 
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v___x_208_, 0);
lean_dec(v_unused_219_);
v___x_210_ = v___x_208_;
v_isShared_211_ = v_isSharedCheck_218_;
goto v_resetjp_209_;
}
else
{
lean_dec(v___x_208_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_218_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v_defValue_200_);
lean_ctor_set(v___x_203_, 0, v_name_196_);
v___x_213_ = v___x_203_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_name_196_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_defValue_200_);
v___x_213_ = v_reuseFailAlloc_217_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_215_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 0, v___x_213_);
v___x_215_ = v___x_210_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
else
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
lean_del_object(v___x_203_);
lean_dec(v_defValue_200_);
lean_dec(v_name_196_);
v_a_220_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_208_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_208_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_229_, lean_object* v_decl_230_, lean_object* v_ref_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__spec__0(v_name_229_, v_decl_230_, v_ref_231_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_250_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_));
v___x_251_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_));
v___x_252_ = ((lean_object*)(l_Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_));
v___x_253_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__spec__0(v___x_250_, v___x_251_, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4____boxed(lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_();
return v_res_255_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_getSanitizeNames_spec__0(lean_object* v_opts_256_, lean_object* v_opt_257_){
_start:
{
lean_object* v_name_258_; lean_object* v_defValue_259_; lean_object* v_map_260_; lean_object* v___x_261_; 
v_name_258_ = lean_ctor_get(v_opt_257_, 0);
v_defValue_259_ = lean_ctor_get(v_opt_257_, 1);
v_map_260_ = lean_ctor_get(v_opts_256_, 0);
v___x_261_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_260_, v_name_258_);
if (lean_obj_tag(v___x_261_) == 0)
{
uint8_t v___x_262_; 
v___x_262_ = lean_unbox(v_defValue_259_);
return v___x_262_;
}
else
{
lean_object* v_val_263_; 
v_val_263_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_val_263_);
lean_dec_ref(v___x_261_);
if (lean_obj_tag(v_val_263_) == 1)
{
uint8_t v_v_264_; 
v_v_264_ = lean_ctor_get_uint8(v_val_263_, 0);
lean_dec_ref(v_val_263_);
return v_v_264_;
}
else
{
uint8_t v___x_265_; 
lean_dec(v_val_263_);
v___x_265_ = lean_unbox(v_defValue_259_);
return v___x_265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_getSanitizeNames_spec__0___boxed(lean_object* v_opts_266_, lean_object* v_opt_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_Lean_Option_get___at___00Lean_getSanitizeNames_spec__0(v_opts_266_, v_opt_267_);
lean_dec_ref(v_opt_267_);
lean_dec_ref(v_opts_266_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT uint8_t l_Lean_getSanitizeNames(lean_object* v_o_270_){
_start:
{
lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_271_ = l_Lean_pp_sanitizeNames;
v___x_272_ = l_Lean_Option_get___at___00Lean_getSanitizeNames_spec__0(v_o_270_, v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSanitizeNames___boxed(lean_object* v_o_273_){
_start:
{
uint8_t v_res_274_; lean_object* v_r_275_; 
v_res_274_ = l_Lean_getSanitizeNames(v_o_273_);
lean_dec_ref(v_o_273_);
v_r_275_ = lean_box(v_res_274_);
return v_r_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkFreshInaccessibleUserName(lean_object* v_userName_276_, lean_object* v_idx_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_options_279_; lean_object* v_nameStem2Idx_280_; lean_object* v_userName2Sanitized_281_; uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_options_279_ = lean_ctor_get(v_a_278_, 0);
v_nameStem2Idx_280_ = lean_ctor_get(v_a_278_, 1);
v_userName2Sanitized_281_ = lean_ctor_get(v_a_278_, 2);
v___x_282_ = l_Std_Format_getUnicode(v_options_279_);
lean_inc(v_idx_277_);
lean_inc(v_userName_276_);
v___x_283_ = l_Lean_Name_num___override(v_userName_276_, v_idx_277_);
v___x_284_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(v___x_282_, v___x_283_);
v___x_285_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v___x_284_, v_nameStem2Idx_280_);
if (v___x_285_ == 0)
{
lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_296_; 
lean_inc(v_userName2Sanitized_281_);
lean_inc(v_nameStem2Idx_280_);
lean_inc_ref(v_options_279_);
v_isSharedCheck_296_ = !lean_is_exclusive(v_a_278_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; lean_object* v_unused_298_; lean_object* v_unused_299_; 
v_unused_297_ = lean_ctor_get(v_a_278_, 2);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_a_278_, 1);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v_a_278_, 0);
lean_dec(v_unused_299_);
v___x_287_ = v_a_278_;
v_isShared_288_ = v_isSharedCheck_296_;
goto v_resetjp_286_;
}
else
{
lean_dec(v_a_278_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_296_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_nat_add(v_idx_277_, v___x_289_);
lean_dec(v_idx_277_);
v___x_291_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_userName_276_, v___x_290_, v_nameStem2Idx_280_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 1, v___x_291_);
v___x_293_ = v___x_287_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_options_279_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_295_, 2, v_userName2Sanitized_281_);
v___x_293_ = v_reuseFailAlloc_295_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_294_; 
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_284_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
return v___x_294_;
}
}
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v___x_284_);
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = lean_nat_add(v_idx_277_, v___x_300_);
lean_dec(v_idx_277_);
v_idx_277_ = v___x_301_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_sanitizeName(lean_object* v_userName_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_nameStem2Idx_305_; lean_object* v_stem_306_; lean_object* v___y_308_; lean_object* v___x_330_; 
v_nameStem2Idx_305_ = lean_ctor_get(v_a_304_, 1);
lean_inc(v_userName_303_);
v_stem_306_ = lean_erase_macro_scopes(v_userName_303_);
v___x_330_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_nameStem2Idx_305_, v_stem_306_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v___x_331_; 
v___x_331_ = lean_unsigned_to_nat(0u);
v___y_308_ = v___x_331_;
goto v___jp_307_;
}
else
{
lean_object* v_val_332_; 
v_val_332_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_val_332_);
lean_dec_ref(v___x_330_);
v___y_308_ = v_val_332_;
goto v___jp_307_;
}
v___jp_307_:
{
lean_object* v___x_309_; lean_object* v_snd_310_; lean_object* v_fst_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_329_; 
v___x_309_ = l___private_Lean_Hygiene_0__Lean_mkFreshInaccessibleUserName(v_stem_306_, v___y_308_, v_a_304_);
v_snd_310_ = lean_ctor_get(v___x_309_, 1);
v_fst_311_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_329_ == 0)
{
v___x_313_ = v___x_309_;
v_isShared_314_ = v_isSharedCheck_329_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_snd_310_);
lean_inc(v_fst_311_);
lean_dec(v___x_309_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_329_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v_options_315_; lean_object* v_nameStem2Idx_316_; lean_object* v_userName2Sanitized_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_328_; 
v_options_315_ = lean_ctor_get(v_snd_310_, 0);
v_nameStem2Idx_316_ = lean_ctor_get(v_snd_310_, 1);
v_userName2Sanitized_317_ = lean_ctor_get(v_snd_310_, 2);
v_isSharedCheck_328_ = !lean_is_exclusive(v_snd_310_);
if (v_isSharedCheck_328_ == 0)
{
v___x_319_ = v_snd_310_;
v_isShared_320_ = v_isSharedCheck_328_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_userName2Sanitized_317_);
lean_inc(v_nameStem2Idx_316_);
lean_inc(v_options_315_);
lean_dec(v_snd_310_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_328_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; lean_object* v___x_323_; 
lean_inc(v_fst_311_);
v___x_321_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_userName_303_, v_fst_311_, v_userName2Sanitized_317_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 2, v___x_321_);
v___x_323_ = v___x_319_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_options_315_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_nameStem2Idx_316_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v___x_321_);
v___x_323_ = v_reuseFailAlloc_327_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_325_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v___x_323_);
v___x_325_ = v___x_313_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_fst_311_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux(lean_object* v_x_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_n_336_; lean_object* v___y_337_; 
switch(lean_obj_tag(v_x_333_))
{
case 3:
{
lean_object* v_val_341_; lean_object* v_userName2Sanitized_342_; lean_object* v___x_343_; 
v_val_341_ = lean_ctor_get(v_x_333_, 2);
v_userName2Sanitized_342_ = lean_ctor_get(v_a_334_, 2);
v___x_343_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_userName2Sanitized_342_, v_val_341_);
if (lean_obj_tag(v___x_343_) == 0)
{
uint8_t v___x_344_; 
v___x_344_ = l_Lean_Name_hasMacroScopes(v_val_341_);
if (v___x_344_ == 0)
{
lean_inc(v_val_341_);
v_n_336_ = v_val_341_;
v___y_337_ = v_a_334_;
goto v___jp_335_;
}
else
{
lean_object* v___x_345_; lean_object* v_fst_346_; lean_object* v_snd_347_; 
lean_inc(v_val_341_);
v___x_345_ = l_Lean_sanitizeName(v_val_341_, v_a_334_);
v_fst_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_fst_346_);
v_snd_347_ = lean_ctor_get(v___x_345_, 1);
lean_inc(v_snd_347_);
lean_dec_ref(v___x_345_);
v_n_336_ = v_fst_346_;
v___y_337_ = v_snd_347_;
goto v___jp_335_;
}
}
else
{
lean_object* v_val_348_; 
v_val_348_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_val_348_);
lean_dec_ref(v___x_343_);
v_n_336_ = v_val_348_;
v___y_337_ = v_a_334_;
goto v___jp_335_;
}
}
case 1:
{
lean_object* v_info_349_; lean_object* v_kind_350_; lean_object* v_args_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_370_; 
v_info_349_ = lean_ctor_get(v_x_333_, 0);
v_kind_350_ = lean_ctor_get(v_x_333_, 1);
v_args_351_ = lean_ctor_get(v_x_333_, 2);
v_isSharedCheck_370_ = !lean_is_exclusive(v_x_333_);
if (v_isSharedCheck_370_ == 0)
{
v___x_353_ = v_x_333_;
v_isShared_354_ = v_isSharedCheck_370_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_args_351_);
lean_inc(v_kind_350_);
lean_inc(v_info_349_);
lean_dec(v_x_333_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_370_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
size_t v_sz_355_; size_t v___x_356_; lean_object* v___x_357_; lean_object* v_fst_358_; lean_object* v_snd_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_369_; 
v_sz_355_ = lean_array_size(v_args_351_);
v___x_356_ = ((size_t)0ULL);
v___x_357_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux_spec__0(v_sz_355_, v___x_356_, v_args_351_, v_a_334_);
v_fst_358_ = lean_ctor_get(v___x_357_, 0);
v_snd_359_ = lean_ctor_get(v___x_357_, 1);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_369_ == 0)
{
v___x_361_ = v___x_357_;
v_isShared_362_ = v_isSharedCheck_369_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_snd_359_);
lean_inc(v_fst_358_);
lean_dec(v___x_357_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_369_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 2, v_fst_358_);
v___x_364_ = v___x_353_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_info_349_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_kind_350_);
lean_ctor_set(v_reuseFailAlloc_368_, 2, v_fst_358_);
v___x_364_ = v_reuseFailAlloc_368_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_366_; 
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_364_);
v___x_366_ = v___x_361_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_snd_359_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
default: 
{
lean_object* v___x_371_; 
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v_x_333_);
lean_ctor_set(v___x_371_, 1, v_a_334_);
return v___x_371_;
}
}
v___jp_335_:
{
uint8_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = 0;
v___x_339_ = l_Lean_mkIdentFrom(v_x_333_, v_n_336_, v___x_338_);
lean_dec(v_x_333_);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___y_337_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux_spec__0(size_t v_sz_372_, size_t v_i_373_, lean_object* v_bs_374_, lean_object* v___y_375_){
_start:
{
uint8_t v___x_376_; 
v___x_376_ = lean_usize_dec_lt(v_i_373_, v_sz_372_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v_bs_374_);
lean_ctor_set(v___x_377_, 1, v___y_375_);
return v___x_377_;
}
else
{
lean_object* v_v_378_; lean_object* v___x_379_; lean_object* v_fst_380_; lean_object* v_snd_381_; lean_object* v___x_382_; lean_object* v_bs_x27_383_; size_t v___x_384_; size_t v___x_385_; lean_object* v___x_386_; 
v_v_378_ = lean_array_uget_borrowed(v_bs_374_, v_i_373_);
lean_inc(v_v_378_);
v___x_379_ = l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux(v_v_378_, v___y_375_);
v_fst_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_fst_380_);
v_snd_381_ = lean_ctor_get(v___x_379_, 1);
lean_inc(v_snd_381_);
lean_dec_ref(v___x_379_);
v___x_382_ = lean_unsigned_to_nat(0u);
v_bs_x27_383_ = lean_array_uset(v_bs_374_, v_i_373_, v___x_382_);
v___x_384_ = ((size_t)1ULL);
v___x_385_ = lean_usize_add(v_i_373_, v___x_384_);
v___x_386_ = lean_array_uset(v_bs_x27_383_, v_i_373_, v_fst_380_);
v_i_373_ = v___x_385_;
v_bs_374_ = v___x_386_;
v___y_375_ = v_snd_381_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux_spec__0___boxed(lean_object* v_sz_388_, lean_object* v_i_389_, lean_object* v_bs_390_, lean_object* v___y_391_){
_start:
{
size_t v_sz_boxed_392_; size_t v_i_boxed_393_; lean_object* v_res_394_; 
v_sz_boxed_392_ = lean_unbox_usize(v_sz_388_);
lean_dec(v_sz_388_);
v_i_boxed_393_ = lean_unbox_usize(v_i_389_);
lean_dec(v_i_389_);
v_res_394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux_spec__0(v_sz_boxed_392_, v_i_boxed_393_, v_bs_390_, v___y_391_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_sanitizeSyntax(lean_object* v_stx_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_options_397_; uint8_t v___x_398_; 
v_options_397_ = lean_ctor_get(v_a_396_, 0);
v___x_398_ = l_Lean_getSanitizeNames(v_options_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_stx_395_);
lean_ctor_set(v___x_399_, 1, v_a_396_);
return v___x_399_;
}
else
{
lean_object* v___x_400_; 
v___x_400_ = l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux(v_stx_395_, v_a_396_);
return v___x_400_;
}
}
}
lean_object* runtime_initialize_Lean_Data_Format(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Hygiene(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_sanitizeNames = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_sanitizeNames);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Hygiene(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Format(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Hygiene(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Hygiene(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Hygiene(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Hygiene(builtin);
}
#ifdef __cplusplus
}
#endif
