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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
uint8_t l_Lean_Std_Format_getUnicode(lean_object*);
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
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Hygiene_0__Lean_initFn___closed__0_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l___private_Lean_Hygiene_0__Lean_initFn___closed__0_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Hygiene_0__Lean_initFn___closed__0_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Hygiene_0__Lean_initFn___closed__1_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "sanitizeNames"};
static const lean_object* l___private_Lean_Hygiene_0__Lean_initFn___closed__1_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Hygiene_0__Lean_initFn___closed__1_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Hygiene_0__Lean_initFn___closed__2_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Hygiene_0__Lean_initFn___closed__0_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l___private_Lean_Hygiene_0__Lean_initFn___closed__2_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Hygiene_0__Lean_initFn___closed__2_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Hygiene_0__Lean_initFn___closed__1_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(147, 143, 157, 1, 169, 13, 114, 103)}};
static const lean_object* l___private_Lean_Hygiene_0__Lean_initFn___closed__2_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Hygiene_0__Lean_initFn___closed__2_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Hygiene_0__Lean_initFn___closed__3_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "add suffix to shadowed/inaccessible variables when pretty printing"};
static const lean_object* l___private_Lean_Hygiene_0__Lean_initFn___closed__3_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Hygiene_0__Lean_initFn___closed__3_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Hygiene_0__Lean_initFn___closed__4_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Hygiene_0__Lean_initFn___closed__3_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Hygiene_0__Lean_initFn___closed__4_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Hygiene_0__Lean_initFn___closed__4_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Hygiene_0__Lean_initFn___closed__5_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Hygiene_0__Lean_initFn___closed__5_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Hygiene_0__Lean_initFn___closed__5_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Hygiene_0__Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Hygiene_0__Lean_initFn___closed__5_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Hygiene_0__Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Hygiene_0__Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Hygiene_0__Lean_initFn___closed__0_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(72, 7, 204, 203, 213, 214, 129, 229)}};
static const lean_ctor_object l___private_Lean_Hygiene_0__Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Hygiene_0__Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Hygiene_0__Lean_initFn___closed__1_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(110, 75, 30, 190, 199, 100, 219, 176)}};
static const lean_object* l___private_Lean_Hygiene_0__Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Hygiene_0__Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4____boxed(lean_object*);
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
lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux(uint8_t v_unicode_156_, lean_object* v_name_157_, lean_object* v_idx_158_){
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
LEAN_EXPORT void l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux_0interp(lean_interpreter_value* stack)
{
uint8_t v_unicode_156_ = stack[0].m_num;
lean_object* v_name_157_ = stack[1].m_obj;
lean_object* v_idx_158_ = stack[2].m_obj;
lean_object* v_res_170_;
v_res_170_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux(v_unicode_156_, v_name_157_, v_idx_158_);
stack->m_obj
 = v_res_170_;
}
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___boxed(lean_object* v_unicode_171_, lean_object* v_name_172_, lean_object* v_idx_173_){
_start:
{
uint8_t v_unicode_boxed_174_; lean_object* v_res_175_; 
v_unicode_boxed_174_ = lean_unbox(v_unicode_171_);
v_res_175_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux(v_unicode_boxed_174_, v_name_172_, v_idx_173_);
return v_res_175_;
}
}
lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(uint8_t v_unicode_177_, lean_object* v_x_178_){
_start:
{
if (lean_obj_tag(v_x_178_) == 2)
{
lean_object* v_pre_179_; 
v_pre_179_ = lean_ctor_get(v_x_178_, 0);
lean_inc(v_pre_179_);
switch(lean_obj_tag(v_pre_179_))
{
case 1:
{
lean_object* v_i_180_; lean_object* v___x_181_; 
v_i_180_ = lean_ctor_get(v_x_178_, 1);
lean_inc(v_i_180_);
lean_dec_ref_known(v_x_178_, 2);
v___x_181_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux(v_unicode_177_, v_pre_179_, v_i_180_);
return v___x_181_;
}
case 0:
{
lean_object* v_i_182_; lean_object* v___x_183_; 
v_i_182_ = lean_ctor_get(v_x_178_, 1);
lean_inc(v_i_182_);
lean_dec_ref_known(v_x_178_, 2);
v___x_183_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux(v_unicode_177_, v_pre_179_, v_i_182_);
return v___x_183_;
}
default: 
{
if (v_unicode_177_ == 0)
{
lean_object* v_i_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_i_184_ = lean_ctor_get(v_x_178_, 1);
lean_inc(v_i_184_);
lean_dec_ref_known(v_x_178_, 2);
v___x_185_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(v_unicode_177_, v_pre_179_);
v___x_186_ = l_Lean_Name_num___override(v___x_185_, v_i_184_);
return v___x_186_;
}
else
{
lean_object* v_i_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_i_187_ = lean_ctor_get(v_x_178_, 1);
lean_inc(v_i_187_);
lean_dec_ref_known(v_x_178_, 2);
v___x_188_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(v_unicode_177_, v_pre_179_);
v___x_189_ = ((lean_object*)(l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___closed__0));
v___x_190_ = l_Nat_toSuperscriptString(v_i_187_);
v___x_191_ = lean_string_append(v___x_189_, v___x_190_);
lean_dec_ref(v___x_190_);
v___x_192_ = lean_name_append_after(v___x_188_, v___x_191_);
return v___x_192_;
}
}
}
}
else
{
return v_x_178_;
}
}
}
LEAN_EXPORT void l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName_0interp(lean_interpreter_value* stack)
{
uint8_t v_unicode_177_ = stack[0].m_num;
lean_object* v_x_178_ = stack[1].m_obj;
lean_object* v_res_193_;
v_res_193_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(v_unicode_177_, v_x_178_);
stack->m_obj
 = v_res_193_;
}
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___boxed(lean_object* v_unicode_194_, lean_object* v_x_195_){
_start:
{
uint8_t v_unicode_boxed_196_; lean_object* v_res_197_; 
v_unicode_boxed_196_ = lean_unbox(v_unicode_194_);
v_res_197_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(v_unicode_boxed_196_, v_x_195_);
return v_res_197_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__spec__0(lean_object* v_name_198_, lean_object* v_decl_199_, lean_object* v_ref_200_){
_start:
{
lean_object* v_defValue_202_; lean_object* v_descr_203_; lean_object* v_deprecation_x3f_204_; lean_object* v___x_205_; uint8_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_defValue_202_ = lean_ctor_get(v_decl_199_, 0);
v_descr_203_ = lean_ctor_get(v_decl_199_, 1);
v_deprecation_x3f_204_ = lean_ctor_get(v_decl_199_, 2);
v___x_205_ = lean_alloc_ctor(1, 0, 1);
v___x_206_ = lean_unbox(v_defValue_202_);
lean_ctor_set_uint8(v___x_205_, 0, v___x_206_);
lean_inc(v_deprecation_x3f_204_);
lean_inc_ref(v_descr_203_);
lean_inc_n(v_name_198_, 2);
v___x_207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_207_, 0, v_name_198_);
lean_ctor_set(v___x_207_, 1, v_ref_200_);
lean_ctor_set(v___x_207_, 2, v___x_205_);
lean_ctor_set(v___x_207_, 3, v_descr_203_);
lean_ctor_set(v___x_207_, 4, v_deprecation_x3f_204_);
v___x_208_ = lean_register_option(v_name_198_, v___x_207_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_216_; 
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_216_ == 0)
{
lean_object* v_unused_217_; 
v_unused_217_ = lean_ctor_get(v___x_208_, 0);
lean_dec(v_unused_217_);
v___x_210_ = v___x_208_;
v_isShared_211_ = v_isSharedCheck_216_;
goto v_resetjp_209_;
}
else
{
lean_dec(v___x_208_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_216_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v___x_214_; 
lean_inc(v_defValue_202_);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v_name_198_);
lean_ctor_set(v___x_212_, 1, v_defValue_202_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 0, v___x_212_);
v___x_214_ = v___x_210_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
else
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
lean_dec(v_name_198_);
v_a_218_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_208_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_208_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_198_ = stack[0].m_obj;
lean_object* v_decl_199_ = stack[1].m_obj;
lean_object* v_ref_200_ = stack[2].m_obj;
lean_object* v_res_226_;
v_res_226_ = l_Lean_Option_register___at___00__private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__spec__0(v_name_198_, v_decl_199_, v_ref_200_);
stack->m_obj
 = v_res_226_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_227_, lean_object* v_decl_228_, lean_object* v_ref_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Option_register___at___00__private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__spec__0(v_name_227_, v_decl_228_, v_ref_229_);
lean_dec_ref(v_decl_228_);
return v_res_231_;
}
}
lean_object* l___private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_249_ = ((lean_object*)(l___private_Lean_Hygiene_0__Lean_initFn___closed__2_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_));
v___x_250_ = ((lean_object*)(l___private_Lean_Hygiene_0__Lean_initFn___closed__4_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_));
v___x_251_ = ((lean_object*)(l___private_Lean_Hygiene_0__Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_));
v___x_252_ = l_Lean_Option_register___at___00__private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__spec__0(v___x_249_, v___x_250_, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT void l___private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_253_;
v_res_253_ = l___private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_();
stack->m_obj
 = v_res_253_;
}
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4____boxed(lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_();
return v_res_255_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_getSanitizeNames_spec__0(lean_object* v_opts_256_, lean_object* v_opt_257_){
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
lean_dec_ref_known(v___x_261_, 1);
if (lean_obj_tag(v_val_263_) == 1)
{
uint8_t v_v_264_; 
v_v_264_ = lean_ctor_get_uint8(v_val_263_, 0);
lean_dec_ref_known(v_val_263_, 0);
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
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_getSanitizeNames_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_256_ = stack[0].m_obj;
lean_object* v_opt_257_ = stack[1].m_obj;
uint8_t v_res_266_;
v_res_266_ = l_Lean_Option_get___at___00Lean_getSanitizeNames_spec__0(v_opts_256_, v_opt_257_);
stack->m_num = v_res_266_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_getSanitizeNames_spec__0___boxed(lean_object* v_opts_267_, lean_object* v_opt_268_){
_start:
{
uint8_t v_res_269_; lean_object* v_r_270_; 
v_res_269_ = l_Lean_Option_get___at___00Lean_getSanitizeNames_spec__0(v_opts_267_, v_opt_268_);
lean_dec_ref(v_opt_268_);
lean_dec_ref(v_opts_267_);
v_r_270_ = lean_box(v_res_269_);
return v_r_270_;
}
}
uint8_t l_Lean_getSanitizeNames(lean_object* v_o_271_){
_start:
{
lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_272_ = l_Lean_pp_sanitizeNames;
v___x_273_ = l_Lean_Option_get___at___00Lean_getSanitizeNames_spec__0(v_o_271_, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT void l_Lean_getSanitizeNames_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_271_ = stack[0].m_obj;
uint8_t v_res_274_;
v_res_274_ = l_Lean_getSanitizeNames(v_o_271_);
stack->m_num = v_res_274_;
}
LEAN_EXPORT lean_object* l_Lean_getSanitizeNames___boxed(lean_object* v_o_275_){
_start:
{
uint8_t v_res_276_; lean_object* v_r_277_; 
v_res_276_ = l_Lean_getSanitizeNames(v_o_275_);
lean_dec_ref(v_o_275_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkFreshInaccessibleUserName(lean_object* v_userName_278_, lean_object* v_idx_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_options_281_; lean_object* v_nameStem2Idx_282_; lean_object* v_userName2Sanitized_283_; uint8_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v_options_281_ = lean_ctor_get(v_a_280_, 0);
v_nameStem2Idx_282_ = lean_ctor_get(v_a_280_, 1);
v_userName2Sanitized_283_ = lean_ctor_get(v_a_280_, 2);
v___x_284_ = l_Lean_Std_Format_getUnicode(v_options_281_);
lean_inc(v_idx_279_);
lean_inc(v_userName_278_);
v___x_285_ = l_Lean_Name_num___override(v_userName_278_, v_idx_279_);
v___x_286_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(v___x_284_, v___x_285_);
v___x_287_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v___x_286_, v_nameStem2Idx_282_);
if (v___x_287_ == 0)
{
lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_298_; 
lean_inc(v_userName2Sanitized_283_);
lean_inc(v_nameStem2Idx_282_);
lean_inc_ref(v_options_281_);
v_isSharedCheck_298_ = !lean_is_exclusive(v_a_280_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; lean_object* v_unused_300_; lean_object* v_unused_301_; 
v_unused_299_ = lean_ctor_get(v_a_280_, 2);
lean_dec(v_unused_299_);
v_unused_300_ = lean_ctor_get(v_a_280_, 1);
lean_dec(v_unused_300_);
v_unused_301_ = lean_ctor_get(v_a_280_, 0);
lean_dec(v_unused_301_);
v___x_289_ = v_a_280_;
v_isShared_290_ = v_isSharedCheck_298_;
goto v_resetjp_288_;
}
else
{
lean_dec(v_a_280_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_298_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = lean_nat_add(v_idx_279_, v___x_291_);
lean_dec(v_idx_279_);
v___x_293_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_userName_278_, v___x_292_, v_nameStem2Idx_282_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 1, v___x_293_);
v___x_295_ = v___x_289_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_options_281_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_297_, 2, v_userName2Sanitized_283_);
v___x_295_ = v_reuseFailAlloc_297_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_296_; 
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_286_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
return v___x_296_;
}
}
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec(v___x_286_);
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = lean_nat_add(v_idx_279_, v___x_302_);
lean_dec(v_idx_279_);
v_idx_279_ = v___x_303_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_sanitizeName(lean_object* v_userName_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_nameStem2Idx_307_; lean_object* v_stem_308_; lean_object* v___y_310_; lean_object* v___x_332_; 
v_nameStem2Idx_307_ = lean_ctor_get(v_a_306_, 1);
v_stem_308_ = l_Lean_Name_eraseMacroScopes(v_userName_305_);
v___x_332_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_nameStem2Idx_307_, v_stem_308_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v___x_333_; 
v___x_333_ = lean_unsigned_to_nat(0u);
v___y_310_ = v___x_333_;
goto v___jp_309_;
}
else
{
lean_object* v_val_334_; 
v_val_334_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_val_334_);
lean_dec_ref_known(v___x_332_, 1);
v___y_310_ = v_val_334_;
goto v___jp_309_;
}
v___jp_309_:
{
lean_object* v___x_311_; lean_object* v_snd_312_; lean_object* v_fst_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_331_; 
v___x_311_ = l___private_Lean_Hygiene_0__Lean_mkFreshInaccessibleUserName(v_stem_308_, v___y_310_, v_a_306_);
v_snd_312_ = lean_ctor_get(v___x_311_, 1);
v_fst_313_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_331_ == 0)
{
v___x_315_ = v___x_311_;
v_isShared_316_ = v_isSharedCheck_331_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_snd_312_);
lean_inc(v_fst_313_);
lean_dec(v___x_311_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_331_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v_options_317_; lean_object* v_nameStem2Idx_318_; lean_object* v_userName2Sanitized_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_330_; 
v_options_317_ = lean_ctor_get(v_snd_312_, 0);
v_nameStem2Idx_318_ = lean_ctor_get(v_snd_312_, 1);
v_userName2Sanitized_319_ = lean_ctor_get(v_snd_312_, 2);
v_isSharedCheck_330_ = !lean_is_exclusive(v_snd_312_);
if (v_isSharedCheck_330_ == 0)
{
v___x_321_ = v_snd_312_;
v_isShared_322_ = v_isSharedCheck_330_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_userName2Sanitized_319_);
lean_inc(v_nameStem2Idx_318_);
lean_inc(v_options_317_);
lean_dec(v_snd_312_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_330_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_325_; 
lean_inc(v_fst_313_);
v___x_323_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_userName_305_, v_fst_313_, v_userName2Sanitized_319_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 2, v___x_323_);
v___x_325_ = v___x_321_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_options_317_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_nameStem2Idx_318_);
lean_ctor_set(v_reuseFailAlloc_329_, 2, v___x_323_);
v___x_325_ = v_reuseFailAlloc_329_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_327_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 1, v___x_325_);
v___x_327_ = v___x_315_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_fst_313_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux(lean_object* v_x_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_n_338_; lean_object* v___y_339_; 
switch(lean_obj_tag(v_x_335_))
{
case 3:
{
lean_object* v_val_343_; lean_object* v_userName2Sanitized_344_; lean_object* v___x_345_; 
v_val_343_ = lean_ctor_get(v_x_335_, 2);
v_userName2Sanitized_344_ = lean_ctor_get(v_a_336_, 2);
v___x_345_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_userName2Sanitized_344_, v_val_343_);
if (lean_obj_tag(v___x_345_) == 0)
{
uint8_t v___x_346_; 
v___x_346_ = l_Lean_Name_hasMacroScopes(v_val_343_);
if (v___x_346_ == 0)
{
lean_inc(v_val_343_);
v_n_338_ = v_val_343_;
v___y_339_ = v_a_336_;
goto v___jp_337_;
}
else
{
lean_object* v___x_347_; lean_object* v_fst_348_; lean_object* v_snd_349_; 
lean_inc(v_val_343_);
v___x_347_ = l_Lean_sanitizeName(v_val_343_, v_a_336_);
v_fst_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_fst_348_);
v_snd_349_ = lean_ctor_get(v___x_347_, 1);
lean_inc(v_snd_349_);
lean_dec_ref(v___x_347_);
v_n_338_ = v_fst_348_;
v___y_339_ = v_snd_349_;
goto v___jp_337_;
}
}
else
{
lean_object* v_val_350_; 
v_val_350_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_val_350_);
lean_dec_ref_known(v___x_345_, 1);
v_n_338_ = v_val_350_;
v___y_339_ = v_a_336_;
goto v___jp_337_;
}
}
case 1:
{
lean_object* v_info_351_; lean_object* v_kind_352_; lean_object* v_args_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_372_; 
v_info_351_ = lean_ctor_get(v_x_335_, 0);
v_kind_352_ = lean_ctor_get(v_x_335_, 1);
v_args_353_ = lean_ctor_get(v_x_335_, 2);
v_isSharedCheck_372_ = !lean_is_exclusive(v_x_335_);
if (v_isSharedCheck_372_ == 0)
{
v___x_355_ = v_x_335_;
v_isShared_356_ = v_isSharedCheck_372_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_args_353_);
lean_inc(v_kind_352_);
lean_inc(v_info_351_);
lean_dec(v_x_335_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_372_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
size_t v_sz_357_; size_t v___x_358_; lean_object* v___x_359_; lean_object* v_fst_360_; lean_object* v_snd_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_371_; 
v_sz_357_ = lean_array_size(v_args_353_);
v___x_358_ = ((size_t)0ULL);
v___x_359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux_spec__0(v_sz_357_, v___x_358_, v_args_353_, v_a_336_);
v_fst_360_ = lean_ctor_get(v___x_359_, 0);
v_snd_361_ = lean_ctor_get(v___x_359_, 1);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_371_ == 0)
{
v___x_363_ = v___x_359_;
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_snd_361_);
lean_inc(v_fst_360_);
lean_dec(v___x_359_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 2, v_fst_360_);
v___x_366_ = v___x_355_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_info_351_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_kind_352_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v_fst_360_);
v___x_366_ = v_reuseFailAlloc_370_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_368_; 
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_366_);
v___x_368_ = v___x_363_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_snd_361_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
default: 
{
lean_object* v___x_373_; 
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v_x_335_);
lean_ctor_set(v___x_373_, 1, v_a_336_);
return v___x_373_;
}
}
v___jp_337_:
{
uint8_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = 0;
v___x_341_ = l_Lean_mkIdentFrom(v_x_335_, v_n_338_, v___x_340_);
lean_dec(v_x_335_);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___y_339_);
return v___x_342_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux_spec__0(size_t v_sz_374_, size_t v_i_375_, lean_object* v_bs_376_, lean_object* v___y_377_){
_start:
{
uint8_t v___x_378_; 
v___x_378_ = lean_usize_dec_lt(v_i_375_, v_sz_374_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v_bs_376_);
lean_ctor_set(v___x_379_, 1, v___y_377_);
return v___x_379_;
}
else
{
lean_object* v_v_380_; lean_object* v___x_381_; lean_object* v_fst_382_; lean_object* v_snd_383_; lean_object* v___x_384_; lean_object* v_bs_x27_385_; size_t v___x_386_; size_t v___x_387_; lean_object* v___x_388_; 
v_v_380_ = lean_array_uget_borrowed(v_bs_376_, v_i_375_);
lean_inc(v_v_380_);
v___x_381_ = l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux(v_v_380_, v___y_377_);
v_fst_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_fst_382_);
v_snd_383_ = lean_ctor_get(v___x_381_, 1);
lean_inc(v_snd_383_);
lean_dec_ref(v___x_381_);
v___x_384_ = lean_unsigned_to_nat(0u);
v_bs_x27_385_ = lean_array_uset(v_bs_376_, v_i_375_, v___x_384_);
v___x_386_ = ((size_t)1ULL);
v___x_387_ = lean_usize_add(v_i_375_, v___x_386_);
v___x_388_ = lean_array_uset(v_bs_x27_385_, v_i_375_, v_fst_382_);
v_i_375_ = v___x_387_;
v_bs_376_ = v___x_388_;
v___y_377_ = v_snd_383_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_374_ = stack[0].m_num;
size_t v_i_375_ = stack[1].m_num;
lean_object* v_bs_376_ = stack[2].m_obj;
lean_object* v___y_377_ = stack[3].m_obj;
lean_object* v_res_390_;
v_res_390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux_spec__0(v_sz_374_, v_i_375_, v_bs_376_, v___y_377_);
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux_spec__0___boxed(lean_object* v_sz_391_, lean_object* v_i_392_, lean_object* v_bs_393_, lean_object* v___y_394_){
_start:
{
size_t v_sz_boxed_395_; size_t v_i_boxed_396_; lean_object* v_res_397_; 
v_sz_boxed_395_ = lean_unbox_usize(v_sz_391_);
lean_dec(v_sz_391_);
v_i_boxed_396_ = lean_unbox_usize(v_i_392_);
lean_dec(v_i_392_);
v_res_397_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux_spec__0(v_sz_boxed_395_, v_i_boxed_396_, v_bs_393_, v___y_394_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_sanitizeSyntax(lean_object* v_stx_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_options_400_; uint8_t v___x_401_; 
v_options_400_ = lean_ctor_get(v_a_399_, 0);
v___x_401_ = l_Lean_getSanitizeNames(v_options_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v_stx_398_);
lean_ctor_set(v___x_402_, 1, v_a_399_);
return v___x_402_;
}
else
{
lean_object* v___x_403_; 
v___x_403_ = l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux(v_stx_398_, v_a_399_);
return v___x_403_;
}
}
}
lean_object* runtime_initialize_Lean_Data_Format(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Hygiene(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_();
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
