// Lean compiler output
// Module: Lean.Compiler.IR.NormIds
// Imports: public import Lean.Compiler.IR.Basic
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkId(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkFnBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* l_Lean_IR_Alt_body(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkDecl(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Decl_uniqueIds(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_uniqueIds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normIndex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normIndex___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normJP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normJP___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArg___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normExpr___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_NormalizeIds_withVar___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_NormalizeIds_withVar___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_NormalizeIds_withVar___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_NormalizeIds_withVar___redArg___closed__0 = (const lean_object*)&l_Lean_IR_NormalizeIds_withVar___redArg___closed__0_value;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__0 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__0_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__1 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__1_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__2 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__2_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__3 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__3_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__4 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__4_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__5 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__5_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__6 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__6_value;
static const lean_ctor_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__0_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__1_value)}};
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__7 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__7_value;
static const lean_ctor_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__7_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__2_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__3_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__4_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__5_value)}};
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__8 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__8_value;
static const lean_ctor_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__8_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__6_value)}};
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__9 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value;
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__10 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__10_value;
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__4, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__11 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__11_value;
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__7, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__12 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__12_value;
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__9, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__13 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__13_value;
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_map, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__14 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__14_value;
static const lean_ctor_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__14_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__10_value)}};
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__15 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__15_value;
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_pure, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__16 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__16_value;
static const lean_ctor_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__15_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__16_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__11_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__12_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__13_value)}};
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__17 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__17_value;
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_bind, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__18 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__18_value;
static const lean_ctor_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__17_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__18_value)}};
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__19 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__19_value;
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_NormalizeIds_withParams___redArg___lam__2, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withVar___redArg___closed__0_value)} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__20 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__20_value;
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_instMonadLiftMN___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_NormalizeIds_instMonadLiftMN___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_NormalizeIds_instMonadLiftMN___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_NormalizeIds_instMonadLiftMN___closed__0 = (const lean_object*)&l_Lean_IR_NormalizeIds_instMonadLiftMN___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_NormalizeIds_instMonadLiftMN = (const lean_object*)&l_Lean_IR_NormalizeIds_instMonadLiftMN___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normFnBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapFnBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_mapVars(lean_object*, lean_object*);
uint8_t l_Lean_IR_instBEqVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = lean_nat_dec_lt(x_1, x_3);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_nat_dec_eq(x_1, x_3);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_7;
}
}
else
{
x_2 = x_4;
goto _start;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_289; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_289 = !lean_is_exclusive(x_3);
if (x_289 == 0)
{
x_9 = x_3;
x_10 = x_289;
goto block_288;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = x_289;
goto block_288;
}
block_288:
{
uint8_t x_11; 
x_11 = lean_nat_dec_lt(x_1, x_5);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_nat_dec_eq(x_1, x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_13 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(x_1, x_2, x_8);
x_14 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 4);
lean_inc(x_20);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_nat_mul(x_21, x_15);
x_23 = lean_nat_dec_lt(x_22, x_16);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_24 = lean_nat_add(x_14, x_15);
x_25 = lean_nat_add(x_24, x_16);
lean_dec(x_16);
lean_dec(x_24);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_13);
lean_ctor_set(x_9, 0, x_25);
x_26 = x_9;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_5);
lean_ctor_set(x_28, 2, x_6);
lean_ctor_set(x_28, 3, x_7);
lean_ctor_set(x_28, 4, x_13);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
else
{
lean_object* x_29; uint8_t x_30; uint8_t x_92; 
x_92 = !lean_is_exclusive(x_13);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_13, 4);
lean_dec(x_93);
x_94 = lean_ctor_get(x_13, 3);
lean_dec(x_94);
x_95 = lean_ctor_get(x_13, 2);
lean_dec(x_95);
x_96 = lean_ctor_get(x_13, 1);
lean_dec(x_96);
x_97 = lean_ctor_get(x_13, 0);
lean_dec(x_97);
x_29 = x_13;
x_30 = x_92;
goto block_91;
}
else
{
lean_dec(x_13);
x_29 = lean_box(0);
x_30 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
x_33 = lean_ctor_get(x_19, 2);
x_34 = lean_ctor_get(x_19, 3);
x_35 = lean_ctor_get(x_19, 4);
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_unsigned_to_nat(2u);
x_38 = lean_nat_mul(x_37, x_36);
x_39 = lean_nat_dec_lt(x_31, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; uint8_t x_67; 
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
x_67 = !lean_is_exclusive(x_19);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_19, 4);
lean_dec(x_68);
x_69 = lean_ctor_get(x_19, 3);
lean_dec(x_69);
x_70 = lean_ctor_get(x_19, 2);
lean_dec(x_70);
x_71 = lean_ctor_get(x_19, 1);
lean_dec(x_71);
x_72 = lean_ctor_get(x_19, 0);
lean_dec(x_72);
x_40 = x_19;
x_41 = x_67;
goto block_66;
}
else
{
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_55; 
x_42 = lean_nat_add(x_14, x_15);
x_43 = lean_nat_add(x_42, x_16);
lean_dec(x_16);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_34, 0);
lean_inc(x_64);
x_55 = x_64;
goto block_63;
}
else
{
lean_object* x_65; 
x_65 = lean_unsigned_to_nat(0u);
x_55 = x_65;
goto block_63;
}
block_54:
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_nat_add(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
if (x_41 == 0)
{
lean_ctor_set(x_40, 4, x_20);
lean_ctor_set(x_40, 3, x_35);
lean_ctor_set(x_40, 2, x_18);
lean_ctor_set(x_40, 1, x_17);
lean_ctor_set(x_40, 0, x_47);
x_48 = x_40;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_17);
lean_ctor_set(x_53, 2, x_18);
lean_ctor_set(x_53, 3, x_35);
lean_ctor_set(x_53, 4, x_20);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_48);
lean_ctor_set(x_29, 3, x_44);
lean_ctor_set(x_29, 2, x_33);
lean_ctor_set(x_29, 1, x_32);
lean_ctor_set(x_29, 0, x_43);
x_49 = x_29;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_32);
lean_ctor_set(x_51, 2, x_33);
lean_ctor_set(x_51, 3, x_44);
lean_ctor_set(x_51, 4, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
block_63:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_nat_add(x_42, x_55);
lean_dec(x_55);
lean_dec(x_42);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_34);
lean_ctor_set(x_9, 0, x_56);
x_57 = x_9;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_5);
lean_ctor_set(x_62, 2, x_6);
lean_ctor_set(x_62, 3, x_7);
lean_ctor_set(x_62, 4, x_34);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
x_58 = lean_nat_add(x_14, x_36);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_35, 0);
lean_inc(x_59);
x_44 = x_57;
x_45 = x_58;
x_46 = x_59;
goto block_54;
}
else
{
lean_object* x_60; 
x_60 = lean_unsigned_to_nat(0u);
x_44 = x_57;
x_45 = x_58;
x_46 = x_60;
goto block_54;
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_del_object(x_9);
x_73 = lean_nat_add(x_14, x_15);
x_74 = lean_nat_add(x_73, x_16);
lean_dec(x_16);
x_75 = lean_nat_add(x_73, x_31);
lean_dec(x_73);
lean_inc_ref(x_7);
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_19);
lean_ctor_set(x_29, 3, x_7);
lean_ctor_set(x_29, 2, x_6);
lean_ctor_set(x_29, 1, x_5);
lean_ctor_set(x_29, 0, x_75);
x_76 = x_29;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_90, 0, x_75);
lean_ctor_set(x_90, 1, x_5);
lean_ctor_set(x_90, 2, x_6);
lean_ctor_set(x_90, 3, x_7);
lean_ctor_set(x_90, 4, x_19);
x_76 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_77; uint8_t x_78; uint8_t x_83; 
x_83 = !lean_is_exclusive(x_7);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_7, 4);
lean_dec(x_84);
x_85 = lean_ctor_get(x_7, 3);
lean_dec(x_85);
x_86 = lean_ctor_get(x_7, 2);
lean_dec(x_86);
x_87 = lean_ctor_get(x_7, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_7, 0);
lean_dec(x_88);
x_77 = x_7;
x_78 = x_83;
goto block_82;
}
else
{
lean_dec(x_7);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
lean_ctor_set(x_77, 4, x_20);
lean_ctor_set(x_77, 3, x_76);
lean_ctor_set(x_77, 2, x_18);
lean_ctor_set(x_77, 1, x_17);
lean_ctor_set(x_77, 0, x_74);
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_17);
lean_ctor_set(x_81, 2, x_18);
lean_ctor_set(x_81, 3, x_76);
lean_ctor_set(x_81, 4, x_20);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
}
}
}
else
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_13, 3);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_124; 
x_99 = lean_ctor_get(x_13, 4);
x_100 = lean_ctor_get(x_13, 1);
x_101 = lean_ctor_get(x_13, 2);
x_124 = !lean_is_exclusive(x_13);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_13, 3);
lean_dec(x_125);
x_126 = lean_ctor_get(x_13, 0);
lean_dec(x_126);
x_102 = x_13;
x_103 = x_124;
goto block_123;
}
else
{
lean_inc(x_99);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_13);
x_102 = lean_box(0);
x_103 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_119; 
x_104 = lean_ctor_get(x_98, 1);
x_105 = lean_ctor_get(x_98, 2);
x_119 = !lean_is_exclusive(x_98);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_98, 4);
lean_dec(x_120);
x_121 = lean_ctor_get(x_98, 3);
lean_dec(x_121);
x_122 = lean_ctor_get(x_98, 0);
lean_dec(x_122);
x_106 = x_98;
x_107 = x_119;
goto block_118;
}
else
{
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_98);
x_106 = lean_box(0);
x_107 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_unsigned_to_nat(3u);
lean_inc_n(x_99, 2);
if (x_107 == 0)
{
lean_ctor_set(x_106, 4, x_99);
lean_ctor_set(x_106, 3, x_99);
lean_ctor_set(x_106, 2, x_6);
lean_ctor_set(x_106, 1, x_5);
lean_ctor_set(x_106, 0, x_14);
x_109 = x_106;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_117, 0, x_14);
lean_ctor_set(x_117, 1, x_5);
lean_ctor_set(x_117, 2, x_6);
lean_ctor_set(x_117, 3, x_99);
lean_ctor_set(x_117, 4, x_99);
x_109 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_110; 
lean_inc(x_99);
if (x_103 == 0)
{
lean_ctor_set(x_102, 3, x_99);
lean_ctor_set(x_102, 0, x_14);
x_110 = x_102;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_115, 0, x_14);
lean_ctor_set(x_115, 1, x_100);
lean_ctor_set(x_115, 2, x_101);
lean_ctor_set(x_115, 3, x_99);
lean_ctor_set(x_115, 4, x_99);
x_110 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_111; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_110);
lean_ctor_set(x_9, 3, x_109);
lean_ctor_set(x_9, 2, x_105);
lean_ctor_set(x_9, 1, x_104);
lean_ctor_set(x_9, 0, x_108);
x_111 = x_9;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_104);
lean_ctor_set(x_113, 2, x_105);
lean_ctor_set(x_113, 3, x_109);
lean_ctor_set(x_113, 4, x_110);
x_111 = x_113;
goto block_112;
}
block_112:
{
return x_111;
}
}
}
}
}
}
else
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_13, 4);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_140; 
x_128 = lean_ctor_get(x_13, 1);
x_129 = lean_ctor_get(x_13, 2);
x_140 = !lean_is_exclusive(x_13);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_13, 4);
lean_dec(x_141);
x_142 = lean_ctor_get(x_13, 3);
lean_dec(x_142);
x_143 = lean_ctor_get(x_13, 0);
lean_dec(x_143);
x_130 = x_13;
x_131 = x_140;
goto block_139;
}
else
{
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_13);
x_130 = lean_box(0);
x_131 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_unsigned_to_nat(3u);
if (x_131 == 0)
{
lean_ctor_set(x_130, 4, x_98);
lean_ctor_set(x_130, 2, x_6);
lean_ctor_set(x_130, 1, x_5);
lean_ctor_set(x_130, 0, x_14);
x_133 = x_130;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_138, 0, x_14);
lean_ctor_set(x_138, 1, x_5);
lean_ctor_set(x_138, 2, x_6);
lean_ctor_set(x_138, 3, x_98);
lean_ctor_set(x_138, 4, x_98);
x_133 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_134; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_127);
lean_ctor_set(x_9, 3, x_133);
lean_ctor_set(x_9, 2, x_129);
lean_ctor_set(x_9, 1, x_128);
lean_ctor_set(x_9, 0, x_132);
x_134 = x_9;
goto block_135;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_136, 0, x_132);
lean_ctor_set(x_136, 1, x_128);
lean_ctor_set(x_136, 2, x_129);
lean_ctor_set(x_136, 3, x_133);
lean_ctor_set(x_136, 4, x_127);
x_134 = x_136;
goto block_135;
}
block_135:
{
return x_134;
}
}
}
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_unsigned_to_nat(2u);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_13);
lean_ctor_set(x_9, 3, x_127);
lean_ctor_set(x_9, 0, x_144);
x_145 = x_9;
goto block_146;
}
else
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_5);
lean_ctor_set(x_147, 2, x_6);
lean_ctor_set(x_147, 3, x_127);
lean_ctor_set(x_147, 4, x_13);
x_145 = x_147;
goto block_146;
}
block_146:
{
return x_145;
}
}
}
}
}
else
{
lean_object* x_148; 
lean_dec(x_6);
lean_dec(x_5);
if (x_10 == 0)
{
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 1, x_1);
x_148 = x_9;
goto block_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_150, 0, x_4);
lean_ctor_set(x_150, 1, x_1);
lean_ctor_set(x_150, 2, x_2);
lean_ctor_set(x_150, 3, x_7);
lean_ctor_set(x_150, 4, x_8);
x_148 = x_150;
goto block_149;
}
block_149:
{
return x_148;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_4);
x_151 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(x_1, x_2, x_7);
x_152 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_153 = lean_ctor_get(x_8, 0);
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_151, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_151, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_151, 3);
lean_inc(x_157);
x_158 = lean_ctor_get(x_151, 4);
lean_inc(x_158);
x_159 = lean_unsigned_to_nat(3u);
x_160 = lean_nat_mul(x_159, x_153);
x_161 = lean_nat_dec_lt(x_160, x_154);
lean_dec(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
x_162 = lean_nat_add(x_152, x_154);
lean_dec(x_154);
x_163 = lean_nat_add(x_162, x_153);
lean_dec(x_162);
if (x_10 == 0)
{
lean_ctor_set(x_9, 3, x_151);
lean_ctor_set(x_9, 0, x_163);
x_164 = x_9;
goto block_165;
}
else
{
lean_object* x_166; 
x_166 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_5);
lean_ctor_set(x_166, 2, x_6);
lean_ctor_set(x_166, 3, x_151);
lean_ctor_set(x_166, 4, x_8);
x_164 = x_166;
goto block_165;
}
block_165:
{
return x_164;
}
}
else
{
lean_object* x_167; uint8_t x_168; uint8_t x_232; 
x_232 = !lean_is_exclusive(x_151);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_233 = lean_ctor_get(x_151, 4);
lean_dec(x_233);
x_234 = lean_ctor_get(x_151, 3);
lean_dec(x_234);
x_235 = lean_ctor_get(x_151, 2);
lean_dec(x_235);
x_236 = lean_ctor_get(x_151, 1);
lean_dec(x_236);
x_237 = lean_ctor_get(x_151, 0);
lean_dec(x_237);
x_167 = x_151;
x_168 = x_232;
goto block_231;
}
else
{
lean_dec(x_151);
x_167 = lean_box(0);
x_168 = x_232;
goto block_231;
}
block_231:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_169 = lean_ctor_get(x_157, 0);
x_170 = lean_ctor_get(x_158, 0);
x_171 = lean_ctor_get(x_158, 1);
x_172 = lean_ctor_get(x_158, 2);
x_173 = lean_ctor_get(x_158, 3);
x_174 = lean_ctor_get(x_158, 4);
x_175 = lean_unsigned_to_nat(2u);
x_176 = lean_nat_mul(x_175, x_169);
x_177 = lean_nat_dec_lt(x_170, x_176);
lean_dec(x_176);
if (x_177 == 0)
{
lean_object* x_178; uint8_t x_179; uint8_t x_206; 
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
x_206 = !lean_is_exclusive(x_158);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_207 = lean_ctor_get(x_158, 4);
lean_dec(x_207);
x_208 = lean_ctor_get(x_158, 3);
lean_dec(x_208);
x_209 = lean_ctor_get(x_158, 2);
lean_dec(x_209);
x_210 = lean_ctor_get(x_158, 1);
lean_dec(x_210);
x_211 = lean_ctor_get(x_158, 0);
lean_dec(x_211);
x_178 = x_158;
x_179 = x_206;
goto block_205;
}
else
{
lean_dec(x_158);
x_178 = lean_box(0);
x_179 = x_206;
goto block_205;
}
block_205:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_193; lean_object* x_194; 
x_180 = lean_nat_add(x_152, x_154);
lean_dec(x_154);
x_181 = lean_nat_add(x_180, x_153);
lean_dec(x_180);
x_193 = lean_nat_add(x_152, x_169);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_173, 0);
lean_inc(x_203);
x_194 = x_203;
goto block_202;
}
else
{
lean_object* x_204; 
x_204 = lean_unsigned_to_nat(0u);
x_194 = x_204;
goto block_202;
}
block_192:
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_nat_add(x_182, x_184);
lean_dec(x_184);
lean_dec(x_182);
if (x_179 == 0)
{
lean_ctor_set(x_178, 4, x_8);
lean_ctor_set(x_178, 3, x_174);
lean_ctor_set(x_178, 2, x_6);
lean_ctor_set(x_178, 1, x_5);
lean_ctor_set(x_178, 0, x_185);
x_186 = x_178;
goto block_190;
}
else
{
lean_object* x_191; 
x_191 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_191, 0, x_185);
lean_ctor_set(x_191, 1, x_5);
lean_ctor_set(x_191, 2, x_6);
lean_ctor_set(x_191, 3, x_174);
lean_ctor_set(x_191, 4, x_8);
x_186 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_187; 
if (x_168 == 0)
{
lean_ctor_set(x_167, 4, x_186);
lean_ctor_set(x_167, 3, x_183);
lean_ctor_set(x_167, 2, x_172);
lean_ctor_set(x_167, 1, x_171);
lean_ctor_set(x_167, 0, x_181);
x_187 = x_167;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_189, 0, x_181);
lean_ctor_set(x_189, 1, x_171);
lean_ctor_set(x_189, 2, x_172);
lean_ctor_set(x_189, 3, x_183);
lean_ctor_set(x_189, 4, x_186);
x_187 = x_189;
goto block_188;
}
block_188:
{
return x_187;
}
}
}
block_202:
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_nat_add(x_193, x_194);
lean_dec(x_194);
lean_dec(x_193);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_173);
lean_ctor_set(x_9, 3, x_157);
lean_ctor_set(x_9, 2, x_156);
lean_ctor_set(x_9, 1, x_155);
lean_ctor_set(x_9, 0, x_195);
x_196 = x_9;
goto block_200;
}
else
{
lean_object* x_201; 
x_201 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_201, 0, x_195);
lean_ctor_set(x_201, 1, x_155);
lean_ctor_set(x_201, 2, x_156);
lean_ctor_set(x_201, 3, x_157);
lean_ctor_set(x_201, 4, x_173);
x_196 = x_201;
goto block_200;
}
block_200:
{
lean_object* x_197; 
x_197 = lean_nat_add(x_152, x_153);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_174, 0);
lean_inc(x_198);
x_182 = x_197;
x_183 = x_196;
x_184 = x_198;
goto block_192;
}
else
{
lean_object* x_199; 
x_199 = lean_unsigned_to_nat(0u);
x_182 = x_197;
x_183 = x_196;
x_184 = x_199;
goto block_192;
}
}
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_del_object(x_9);
x_212 = lean_nat_add(x_152, x_154);
lean_dec(x_154);
x_213 = lean_nat_add(x_212, x_153);
lean_dec(x_212);
x_214 = lean_nat_add(x_152, x_153);
x_215 = lean_nat_add(x_214, x_170);
lean_dec(x_214);
lean_inc_ref(x_8);
if (x_168 == 0)
{
lean_ctor_set(x_167, 4, x_8);
lean_ctor_set(x_167, 3, x_158);
lean_ctor_set(x_167, 2, x_6);
lean_ctor_set(x_167, 1, x_5);
lean_ctor_set(x_167, 0, x_215);
x_216 = x_167;
goto block_229;
}
else
{
lean_object* x_230; 
x_230 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_230, 0, x_215);
lean_ctor_set(x_230, 1, x_5);
lean_ctor_set(x_230, 2, x_6);
lean_ctor_set(x_230, 3, x_158);
lean_ctor_set(x_230, 4, x_8);
x_216 = x_230;
goto block_229;
}
block_229:
{
lean_object* x_217; uint8_t x_218; uint8_t x_223; 
x_223 = !lean_is_exclusive(x_8);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_224 = lean_ctor_get(x_8, 4);
lean_dec(x_224);
x_225 = lean_ctor_get(x_8, 3);
lean_dec(x_225);
x_226 = lean_ctor_get(x_8, 2);
lean_dec(x_226);
x_227 = lean_ctor_get(x_8, 1);
lean_dec(x_227);
x_228 = lean_ctor_get(x_8, 0);
lean_dec(x_228);
x_217 = x_8;
x_218 = x_223;
goto block_222;
}
else
{
lean_dec(x_8);
x_217 = lean_box(0);
x_218 = x_223;
goto block_222;
}
block_222:
{
lean_object* x_219; 
if (x_218 == 0)
{
lean_ctor_set(x_217, 4, x_216);
lean_ctor_set(x_217, 3, x_157);
lean_ctor_set(x_217, 2, x_156);
lean_ctor_set(x_217, 1, x_155);
lean_ctor_set(x_217, 0, x_213);
x_219 = x_217;
goto block_220;
}
else
{
lean_object* x_221; 
x_221 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_221, 0, x_213);
lean_ctor_set(x_221, 1, x_155);
lean_ctor_set(x_221, 2, x_156);
lean_ctor_set(x_221, 3, x_157);
lean_ctor_set(x_221, 4, x_216);
x_219 = x_221;
goto block_220;
}
block_220:
{
return x_219;
}
}
}
}
}
}
}
else
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_151, 3);
lean_inc(x_238);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; uint8_t x_252; 
x_239 = lean_ctor_get(x_151, 4);
x_240 = lean_ctor_get(x_151, 1);
x_241 = lean_ctor_get(x_151, 2);
x_252 = !lean_is_exclusive(x_151);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_151, 3);
lean_dec(x_253);
x_254 = lean_ctor_get(x_151, 0);
lean_dec(x_254);
x_242 = x_151;
x_243 = x_252;
goto block_251;
}
else
{
lean_inc(x_239);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_151);
x_242 = lean_box(0);
x_243 = x_252;
goto block_251;
}
block_251:
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_unsigned_to_nat(3u);
lean_inc(x_239);
if (x_243 == 0)
{
lean_ctor_set(x_242, 3, x_239);
lean_ctor_set(x_242, 2, x_6);
lean_ctor_set(x_242, 1, x_5);
lean_ctor_set(x_242, 0, x_152);
x_245 = x_242;
goto block_249;
}
else
{
lean_object* x_250; 
x_250 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_250, 0, x_152);
lean_ctor_set(x_250, 1, x_5);
lean_ctor_set(x_250, 2, x_6);
lean_ctor_set(x_250, 3, x_239);
lean_ctor_set(x_250, 4, x_239);
x_245 = x_250;
goto block_249;
}
block_249:
{
lean_object* x_246; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_245);
lean_ctor_set(x_9, 3, x_238);
lean_ctor_set(x_9, 2, x_241);
lean_ctor_set(x_9, 1, x_240);
lean_ctor_set(x_9, 0, x_244);
x_246 = x_9;
goto block_247;
}
else
{
lean_object* x_248; 
x_248 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_248, 0, x_244);
lean_ctor_set(x_248, 1, x_240);
lean_ctor_set(x_248, 2, x_241);
lean_ctor_set(x_248, 3, x_238);
lean_ctor_set(x_248, 4, x_245);
x_246 = x_248;
goto block_247;
}
block_247:
{
return x_246;
}
}
}
}
else
{
lean_object* x_255; 
x_255 = lean_ctor_get(x_151, 4);
lean_inc(x_255);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; uint8_t x_280; 
x_256 = lean_ctor_get(x_151, 1);
x_257 = lean_ctor_get(x_151, 2);
x_280 = !lean_is_exclusive(x_151);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_151, 4);
lean_dec(x_281);
x_282 = lean_ctor_get(x_151, 3);
lean_dec(x_282);
x_283 = lean_ctor_get(x_151, 0);
lean_dec(x_283);
x_258 = x_151;
x_259 = x_280;
goto block_279;
}
else
{
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_151);
x_258 = lean_box(0);
x_259 = x_280;
goto block_279;
}
block_279:
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; uint8_t x_275; 
x_260 = lean_ctor_get(x_255, 1);
x_261 = lean_ctor_get(x_255, 2);
x_275 = !lean_is_exclusive(x_255);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_255, 4);
lean_dec(x_276);
x_277 = lean_ctor_get(x_255, 3);
lean_dec(x_277);
x_278 = lean_ctor_get(x_255, 0);
lean_dec(x_278);
x_262 = x_255;
x_263 = x_275;
goto block_274;
}
else
{
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_255);
x_262 = lean_box(0);
x_263 = x_275;
goto block_274;
}
block_274:
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_unsigned_to_nat(3u);
if (x_263 == 0)
{
lean_ctor_set(x_262, 4, x_238);
lean_ctor_set(x_262, 3, x_238);
lean_ctor_set(x_262, 2, x_257);
lean_ctor_set(x_262, 1, x_256);
lean_ctor_set(x_262, 0, x_152);
x_265 = x_262;
goto block_272;
}
else
{
lean_object* x_273; 
x_273 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_273, 0, x_152);
lean_ctor_set(x_273, 1, x_256);
lean_ctor_set(x_273, 2, x_257);
lean_ctor_set(x_273, 3, x_238);
lean_ctor_set(x_273, 4, x_238);
x_265 = x_273;
goto block_272;
}
block_272:
{
lean_object* x_266; 
if (x_259 == 0)
{
lean_ctor_set(x_258, 4, x_238);
lean_ctor_set(x_258, 2, x_6);
lean_ctor_set(x_258, 1, x_5);
lean_ctor_set(x_258, 0, x_152);
x_266 = x_258;
goto block_270;
}
else
{
lean_object* x_271; 
x_271 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_271, 0, x_152);
lean_ctor_set(x_271, 1, x_5);
lean_ctor_set(x_271, 2, x_6);
lean_ctor_set(x_271, 3, x_238);
lean_ctor_set(x_271, 4, x_238);
x_266 = x_271;
goto block_270;
}
block_270:
{
lean_object* x_267; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_266);
lean_ctor_set(x_9, 3, x_265);
lean_ctor_set(x_9, 2, x_261);
lean_ctor_set(x_9, 1, x_260);
lean_ctor_set(x_9, 0, x_264);
x_267 = x_9;
goto block_268;
}
else
{
lean_object* x_269; 
x_269 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_269, 0, x_264);
lean_ctor_set(x_269, 1, x_260);
lean_ctor_set(x_269, 2, x_261);
lean_ctor_set(x_269, 3, x_265);
lean_ctor_set(x_269, 4, x_266);
x_267 = x_269;
goto block_268;
}
block_268:
{
return x_267;
}
}
}
}
}
}
else
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_unsigned_to_nat(2u);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_255);
lean_ctor_set(x_9, 3, x_151);
lean_ctor_set(x_9, 0, x_284);
x_285 = x_9;
goto block_286;
}
else
{
lean_object* x_287; 
x_287 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_287, 0, x_284);
lean_ctor_set(x_287, 1, x_5);
lean_ctor_set(x_287, 2, x_6);
lean_ctor_set(x_287, 3, x_151);
lean_ctor_set(x_287, 4, x_255);
x_285 = x_287;
goto block_286;
}
block_286:
{
return x_285;
}
}
}
}
}
}
}
else
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_unsigned_to_nat(1u);
x_291 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_1);
lean_ctor_set(x_291, 2, x_2);
lean_ctor_set(x_291, 3, x_3);
lean_ctor_set(x_291, 4, x_3);
return x_291;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkId(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___redArg(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
if (x_3 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(x_1, x_5, x_2);
x_7 = lean_box(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = lean_box(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_27; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = l_Lean_IR_UniqueIds_checkId(x_7, x_4);
x_9 = lean_ctor_get(x_8, 0);
x_10 = lean_ctor_get(x_8, 1);
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
x_11 = x_8;
x_12 = x_27;
goto block_26;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = x_27;
goto block_26;
}
block_26:
{
uint8_t x_13; uint8_t x_14; 
x_13 = 1;
x_14 = lean_unbox(x_9);
lean_dec(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(x_13);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_15);
x_16 = x_11;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_10);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
else
{
if (x_5 == 0)
{
size_t x_19; size_t x_20; 
lean_del_object(x_11);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_2 = x_20;
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(x_13);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_22);
x_23 = x_11;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_10);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_4);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
x_3 = x_2;
goto block_7;
}
else
{
if (x_10 == 0)
{
x_3 = x_2;
goto block_7;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_9);
x_13 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0(x_1, x_11, x_12, x_2);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec_ref(x_13);
x_3 = x_16;
goto block_7;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_26; 
x_17 = lean_ctor_get(x_13, 1);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_13, 0);
lean_dec(x_27);
x_18 = x_13;
x_19 = x_26;
goto block_25;
}
else
{
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = x_26;
goto block_25;
}
block_25:
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_box(x_20);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_21);
x_22 = x_18;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_17);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
block_7:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 1;
x_5 = lean_box(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UniqueIds_checkParams(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = l_Lean_IR_UniqueIds_checkId(x_8, x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_9);
return x_10;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec_ref(x_10);
x_1 = x_9;
x_2 = x_13;
goto _start;
}
}
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_1, 3);
lean_inc(x_17);
lean_dec_ref(x_1);
x_18 = l_Lean_IR_UniqueIds_checkId(x_15, x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_17);
lean_dec_ref(x_16);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = l_Lean_IR_UniqueIds_checkParams(x_16, x_21);
lean_dec_ref(x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_dec(x_17);
return x_22;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec_ref(x_22);
x_1 = x_17;
x_2 = x_25;
goto _start;
}
}
}
case 9:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_27);
lean_dec_ref(x_1);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_array_get_size(x_27);
x_30 = lean_nat_dec_lt(x_28, x_29);
if (x_30 == 0)
{
lean_dec_ref(x_27);
x_3 = x_2;
goto block_7;
}
else
{
if (x_30 == 0)
{
lean_dec_ref(x_27);
x_3 = x_2;
goto block_7;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_29);
x_33 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(x_27, x_31, x_32, x_2);
lean_dec_ref(x_27);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec_ref(x_33);
x_3 = x_36;
goto block_7;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_46; 
x_37 = lean_ctor_get(x_33, 1);
x_46 = !lean_is_exclusive(x_33);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_33, 0);
lean_dec(x_47);
x_38 = x_33;
x_39 = x_46;
goto block_45;
}
else
{
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_box(0);
x_39 = x_46;
goto block_45;
}
block_45:
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_40 = 0;
x_41 = lean_box(x_40);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_41);
x_42 = x_38;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_37);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
}
default: 
{
uint8_t x_48; 
x_48 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_49;
goto _start;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_1);
x_51 = lean_box(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_2);
return x_52;
}
}
}
block_7:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 1;
x_5 = lean_box(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_27; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = l_Lean_IR_Alt_body(x_6);
x_8 = l_Lean_IR_UniqueIds_checkFnBody(x_7, x_4);
x_9 = lean_ctor_get(x_8, 0);
x_10 = lean_ctor_get(x_8, 1);
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
x_11 = x_8;
x_12 = x_27;
goto block_26;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = x_27;
goto block_26;
}
block_26:
{
uint8_t x_13; uint8_t x_14; 
x_13 = 1;
x_14 = lean_unbox(x_9);
lean_dec(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(x_13);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_15);
x_16 = x_11;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_10);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
else
{
if (x_5 == 0)
{
size_t x_19; size_t x_20; 
lean_del_object(x_11);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_2 = x_20;
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(x_13);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_22);
x_23 = x_11;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_10);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_4);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_Lean_IR_UniqueIds_checkParams(x_3, x_2);
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = l_Lean_IR_UniqueIds_checkFnBody(x_4, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_10);
lean_dec_ref(x_1);
x_11 = l_Lean_IR_UniqueIds_checkParams(x_10, x_2);
lean_dec_ref(x_10);
return x_11;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Decl_uniqueIds(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_box(1);
x_3 = l_Lean_IR_UniqueIds_checkDecl(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_uniqueIds___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_Decl_uniqueIds(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_nat_dec_lt(x_2, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_2, x_3);
if (x_8 == 0)
{
x_1 = x_6;
goto _start;
}
else
{
lean_object* x_10; 
lean_inc(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
}
else
{
x_1 = x_5;
goto _start;
}
}
else
{
lean_object* x_12; 
x_12 = lean_box(0);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normIndex(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normIndex___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normIndex(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normIndex(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normJP(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normIndex(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normJP___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normJP(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
x_4 = x_1;
x_5 = x_11;
goto block_10;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_IR_NormalizeIds_normIndex(x_3, x_2);
lean_dec(x_3);
if (x_5 == 0)
{
lean_ctor_set(x_4, 0, x_6);
x_7 = x_4;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_6);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Lean_IR_NormalizeIds_normArg(x_6, x_1);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_array_size(x_1);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArgs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normArgs(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normExpr(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_12; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
x_5 = x_1;
x_6 = x_12;
goto block_11;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_IR_NormalizeIds_normArgs(x_4, x_2);
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_7);
x_8 = x_5;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_7);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_22; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
x_15 = x_1;
x_16 = x_22;
goto block_21;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_IR_NormalizeIds_normIndex(x_14, x_2);
lean_dec(x_14);
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_17);
x_18 = x_15;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
case 2:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_35; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_26 = lean_ctor_get(x_1, 2);
x_35 = !lean_is_exclusive(x_1);
if (x_35 == 0)
{
x_27 = x_1;
x_28 = x_35;
goto block_34;
}
else
{
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_IR_NormalizeIds_normIndex(x_23, x_2);
lean_dec(x_23);
x_30 = l_Lean_IR_NormalizeIds_normArgs(x_26, x_2);
if (x_28 == 0)
{
lean_ctor_set(x_27, 2, x_30);
lean_ctor_set(x_27, 0, x_29);
x_31 = x_27;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_24);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_25);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
case 3:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_45; 
x_36 = lean_ctor_get(x_1, 0);
x_37 = lean_ctor_get(x_1, 1);
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
x_38 = x_1;
x_39 = x_45;
goto block_44;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Lean_IR_NormalizeIds_normIndex(x_37, x_2);
lean_dec(x_37);
if (x_39 == 0)
{
lean_ctor_set(x_38, 1, x_40);
x_41 = x_38;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
case 4:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_55; 
x_46 = lean_ctor_get(x_1, 0);
x_47 = lean_ctor_get(x_1, 1);
x_55 = !lean_is_exclusive(x_1);
if (x_55 == 0)
{
x_48 = x_1;
x_49 = x_55;
goto block_54;
}
else
{
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_1);
x_48 = lean_box(0);
x_49 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Lean_IR_NormalizeIds_normIndex(x_47, x_2);
lean_dec(x_47);
if (x_49 == 0)
{
lean_ctor_set(x_48, 1, x_50);
x_51 = x_48;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
case 5:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_66; 
x_56 = lean_ctor_get(x_1, 0);
x_57 = lean_ctor_get(x_1, 1);
x_58 = lean_ctor_get(x_1, 2);
x_66 = !lean_is_exclusive(x_1);
if (x_66 == 0)
{
x_59 = x_1;
x_60 = x_66;
goto block_65;
}
else
{
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_1);
x_59 = lean_box(0);
x_60 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_IR_NormalizeIds_normIndex(x_58, x_2);
lean_dec(x_58);
if (x_60 == 0)
{
lean_ctor_set(x_59, 2, x_61);
x_62 = x_59;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_64, 1, x_57);
lean_ctor_set(x_64, 2, x_61);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
case 6:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_76; 
x_67 = lean_ctor_get(x_1, 0);
x_68 = lean_ctor_get(x_1, 1);
x_76 = !lean_is_exclusive(x_1);
if (x_76 == 0)
{
x_69 = x_1;
x_70 = x_76;
goto block_75;
}
else
{
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_1);
x_69 = lean_box(0);
x_70 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Lean_IR_NormalizeIds_normArgs(x_68, x_2);
if (x_70 == 0)
{
lean_ctor_set(x_69, 1, x_71);
x_72 = x_69;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set(x_74, 1, x_71);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
}
case 7:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_86; 
x_77 = lean_ctor_get(x_1, 0);
x_78 = lean_ctor_get(x_1, 1);
x_86 = !lean_is_exclusive(x_1);
if (x_86 == 0)
{
x_79 = x_1;
x_80 = x_86;
goto block_85;
}
else
{
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_1);
x_79 = lean_box(0);
x_80 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_81; lean_object* x_82; 
x_81 = l_Lean_IR_NormalizeIds_normArgs(x_78, x_2);
if (x_80 == 0)
{
lean_ctor_set(x_79, 1, x_81);
x_82 = x_79;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_81);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
case 8:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_97; 
x_87 = lean_ctor_get(x_1, 0);
x_88 = lean_ctor_get(x_1, 1);
x_97 = !lean_is_exclusive(x_1);
if (x_97 == 0)
{
x_89 = x_1;
x_90 = x_97;
goto block_96;
}
else
{
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_1);
x_89 = lean_box(0);
x_90 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = l_Lean_IR_NormalizeIds_normIndex(x_87, x_2);
lean_dec(x_87);
x_92 = l_Lean_IR_NormalizeIds_normArgs(x_88, x_2);
if (x_90 == 0)
{
lean_ctor_set(x_89, 1, x_92);
lean_ctor_set(x_89, 0, x_91);
x_93 = x_89;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_92);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
case 9:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_107; 
x_98 = lean_ctor_get(x_1, 0);
x_99 = lean_ctor_get(x_1, 1);
x_107 = !lean_is_exclusive(x_1);
if (x_107 == 0)
{
x_100 = x_1;
x_101 = x_107;
goto block_106;
}
else
{
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_1);
x_100 = lean_box(0);
x_101 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_102; lean_object* x_103; 
x_102 = l_Lean_IR_NormalizeIds_normIndex(x_99, x_2);
lean_dec(x_99);
if (x_101 == 0)
{
lean_ctor_set(x_100, 1, x_102);
x_103 = x_100;
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_105, 0, x_98);
lean_ctor_set(x_105, 1, x_102);
x_103 = x_105;
goto block_104;
}
block_104:
{
return x_103;
}
}
}
case 10:
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_116; 
x_108 = lean_ctor_get(x_1, 0);
x_116 = !lean_is_exclusive(x_1);
if (x_116 == 0)
{
x_109 = x_1;
x_110 = x_116;
goto block_115;
}
else
{
lean_inc(x_108);
lean_dec(x_1);
x_109 = lean_box(0);
x_110 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_111; lean_object* x_112; 
x_111 = l_Lean_IR_NormalizeIds_normIndex(x_108, x_2);
lean_dec(x_108);
if (x_110 == 0)
{
lean_ctor_set(x_109, 0, x_111);
x_112 = x_109;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_114, 0, x_111);
x_112 = x_114;
goto block_113;
}
block_113:
{
return x_112;
}
}
}
case 11:
{
return x_1;
}
default: 
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_125; 
x_117 = lean_ctor_get(x_1, 0);
x_125 = !lean_is_exclusive(x_1);
if (x_125 == 0)
{
x_118 = x_1;
x_119 = x_125;
goto block_124;
}
else
{
lean_inc(x_117);
lean_dec(x_1);
x_118 = lean_box(0);
x_119 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_120; lean_object* x_121; 
x_120 = l_Lean_IR_NormalizeIds_normIndex(x_117, x_2);
lean_dec(x_117);
if (x_119 == 0)
{
lean_ctor_set(x_118, 0, x_120);
x_121 = x_118;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_123, 0, x_120);
x_121 = x_123;
goto block_122;
}
block_122:
{
return x_121;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normExpr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normExpr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_NormalizeIds_withVar___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_NormalizeIds_withVar___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_4, x_6);
lean_inc(x_4);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_5, x_1, x_4, x_3);
x_9 = lean_apply_3(x_2, x_4, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_5, x_7);
lean_inc(x_5);
x_9 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_6, x_2, x_5, x_4);
x_10 = lean_apply_3(x_3, x_5, x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_4, x_6);
lean_inc(x_4);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_5, x_1, x_4, x_3);
x_9 = lean_apply_3(x_2, x_4, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_5, x_7);
lean_inc(x_5);
x_9 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_6, x_2, x_5, x_4);
x_10 = lean_apply_3(x_3, x_5, x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_13; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_5 = lean_ctor_get(x_2, 1);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
x_6 = x_2;
x_7 = x_13;
goto block_12;
}
else
{
lean_inc(x_5);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_IR_NormalizeIds_normIndex(x_3, x_1);
lean_dec(x_3);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_8);
x_9 = x_6;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_4);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_withParams___redArg___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_4, x_6);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___redArg(x_1, x_5, x_4, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_5 = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__9));
x_18 = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__19));
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_1);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
x_6 = x_3;
x_7 = x_4;
goto block_13;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__20));
x_23 = lean_nat_dec_le(x_20, x_20);
if (x_23 == 0)
{
if (x_21 == 0)
{
x_6 = x_3;
x_7 = x_4;
goto block_13;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_20);
lean_inc_ref(x_1);
x_26 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_18, x_22, x_1, x_24, x_25, x_3);
x_27 = lean_apply_1(x_26, x_4);
x_14 = x_27;
goto block_17;
}
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_20);
lean_inc_ref(x_1);
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_18, x_22, x_1, x_28, x_29, x_3);
x_31 = lean_apply_1(x_30, x_4);
x_14 = x_31;
goto block_17;
}
}
block_13:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_array_size(x_1);
x_10 = 0;
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_5, x_8, x_9, x_10, x_1);
x_12 = lean_apply_3(x_2, x_11, x_6, x_7);
return x_12;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_6 = x_15;
x_7 = x_16;
goto block_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_15; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_6 = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__9));
x_19 = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__19));
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get_size(x_2);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
x_7 = x_4;
x_8 = x_5;
goto block_14;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__20));
x_24 = lean_nat_dec_le(x_21, x_21);
if (x_24 == 0)
{
if (x_22 == 0)
{
x_7 = x_4;
x_8 = x_5;
goto block_14;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_21);
lean_inc_ref(x_2);
x_27 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_19, x_23, x_2, x_25, x_26, x_4);
x_28 = lean_apply_1(x_27, x_5);
x_15 = x_28;
goto block_18;
}
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_21);
lean_inc_ref(x_2);
x_31 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_19, x_23, x_2, x_29, x_30, x_4);
x_32 = lean_apply_1(x_31, x_5);
x_15 = x_32;
goto block_18;
}
}
block_14:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_array_size(x_2);
x_11 = 0;
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_6, x_9, x_10, x_11, x_2);
x_13 = lean_apply_3(x_3, x_12, x_7, x_8);
return x_13;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_7 = x_16;
x_8 = x_17;
goto block_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_instMonadLiftMN___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_2, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_23; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_9 = lean_ctor_get(x_6, 1);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
x_10 = x_6;
x_11 = x_23;
goto block_22;
}
else
{
lean_inc(x_9);
lean_inc(x_7);
lean_dec(x_6);
x_10 = lean_box(0);
x_11 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_4, x_3, x_12);
x_14 = l_Lean_IR_NormalizeIds_normIndex(x_7, x_1);
lean_dec(x_7);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_14);
x_15 = x_10;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_9);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_8);
x_15 = x_21;
goto block_20;
}
block_20:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_18 = lean_array_uset(x_13, x_3, x_15);
x_3 = x_17;
x_4 = x_18;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_7 = lean_array_uget_borrowed(x_1, x_2);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_inc(x_8);
x_11 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(x_8, x_5, x_4);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_11;
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(x_1, x_6, x_7, x_4, x_5);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_28; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_28 = !lean_is_exclusive(x_1);
if (x_28 == 0)
{
x_8 = x_1;
x_9 = x_28;
goto block_27;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_26; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_inc(x_2);
lean_inc(x_3);
x_12 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(x_4, x_3, x_2);
x_13 = l_Lean_IR_NormalizeIds_normFnBody(x_7, x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_ctor_get(x_13, 1);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
x_16 = x_13;
x_17 = x_26;
goto block_25;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_IR_NormalizeIds_normExpr(x_6, x_2);
lean_dec(x_2);
if (x_9 == 0)
{
lean_ctor_set(x_8, 3, x_14);
lean_ctor_set(x_8, 2, x_18);
lean_ctor_set(x_8, 0, x_3);
x_19 = x_8;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_14);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_19);
x_20 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_15);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
case 1:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_75; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
x_31 = lean_ctor_get(x_1, 2);
x_32 = lean_ctor_get(x_1, 3);
x_75 = !lean_is_exclusive(x_1);
if (x_75 == 0)
{
x_33 = x_1;
x_34 = x_75;
goto block_74;
}
else
{
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_1);
x_33 = lean_box(0);
x_34 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_35; lean_object* x_36; lean_object* x_60; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_array_get_size(x_30);
x_66 = lean_nat_dec_lt(x_64, x_65);
if (x_66 == 0)
{
lean_inc(x_2);
x_35 = x_2;
x_36 = x_3;
goto block_59;
}
else
{
uint8_t x_67; 
x_67 = lean_nat_dec_le(x_65, x_65);
if (x_67 == 0)
{
if (x_66 == 0)
{
lean_inc(x_2);
x_35 = x_2;
x_36 = x_3;
goto block_59;
}
else
{
size_t x_68; size_t x_69; lean_object* x_70; 
x_68 = 0;
x_69 = lean_usize_of_nat(x_65);
lean_inc(x_2);
x_70 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(x_30, x_68, x_69, x_2, x_3);
x_60 = x_70;
goto block_63;
}
}
else
{
size_t x_71; size_t x_72; lean_object* x_73; 
x_71 = 0;
x_72 = lean_usize_of_nat(x_65);
lean_inc(x_2);
x_73 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(x_30, x_71, x_72, x_2, x_3);
x_60 = x_73;
goto block_63;
}
}
block_59:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_58; 
lean_inc(x_35);
x_37 = l_Lean_IR_NormalizeIds_normFnBody(x_31, x_35, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_39, x_40);
lean_inc(x_39);
x_42 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(x_29, x_39, x_2);
x_43 = l_Lean_IR_NormalizeIds_normFnBody(x_32, x_42, x_41);
x_44 = lean_ctor_get(x_43, 0);
x_45 = lean_ctor_get(x_43, 1);
x_58 = !lean_is_exclusive(x_43);
if (x_58 == 0)
{
x_46 = x_43;
x_47 = x_58;
goto block_57;
}
else
{
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_43);
x_46 = lean_box(0);
x_47 = x_58;
goto block_57;
}
block_57:
{
size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_array_size(x_30);
x_49 = 0;
x_50 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(x_35, x_48, x_49, x_30);
lean_dec(x_35);
if (x_34 == 0)
{
lean_ctor_set(x_33, 3, x_44);
lean_ctor_set(x_33, 2, x_38);
lean_ctor_set(x_33, 1, x_50);
lean_ctor_set(x_33, 0, x_39);
x_51 = x_33;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_56, 0, x_39);
lean_ctor_set(x_56, 1, x_50);
lean_ctor_set(x_56, 2, x_38);
lean_ctor_set(x_56, 3, x_44);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_47 == 0)
{
lean_ctor_set(x_46, 0, x_51);
x_52 = x_46;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_45);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
block_63:
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_35 = x_61;
x_36 = x_62;
goto block_59;
}
}
}
case 2:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_98; 
x_76 = lean_ctor_get(x_1, 0);
x_77 = lean_ctor_get(x_1, 1);
x_78 = lean_ctor_get(x_1, 2);
x_79 = lean_ctor_get(x_1, 3);
x_98 = !lean_is_exclusive(x_1);
if (x_98 == 0)
{
x_80 = x_1;
x_81 = x_98;
goto block_97;
}
else
{
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_1);
x_80 = lean_box(0);
x_81 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_96; 
x_82 = l_Lean_IR_NormalizeIds_normIndex(x_76, x_2);
lean_dec(x_76);
x_83 = l_Lean_IR_NormalizeIds_normArg(x_78, x_2);
x_84 = l_Lean_IR_NormalizeIds_normFnBody(x_79, x_2, x_3);
x_85 = lean_ctor_get(x_84, 0);
x_86 = lean_ctor_get(x_84, 1);
x_96 = !lean_is_exclusive(x_84);
if (x_96 == 0)
{
x_87 = x_84;
x_88 = x_96;
goto block_95;
}
else
{
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_84);
x_87 = lean_box(0);
x_88 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_89; 
if (x_81 == 0)
{
lean_ctor_set(x_80, 3, x_85);
lean_ctor_set(x_80, 2, x_83);
lean_ctor_set(x_80, 0, x_82);
x_89 = x_80;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_94, 0, x_82);
lean_ctor_set(x_94, 1, x_77);
lean_ctor_set(x_94, 2, x_83);
lean_ctor_set(x_94, 3, x_85);
x_89 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_90; 
if (x_88 == 0)
{
lean_ctor_set(x_87, 0, x_89);
x_90 = x_87;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_86);
x_90 = x_92;
goto block_91;
}
block_91:
{
return x_90;
}
}
}
}
}
case 3:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_119; 
x_99 = lean_ctor_get(x_1, 0);
x_100 = lean_ctor_get(x_1, 1);
x_101 = lean_ctor_get(x_1, 2);
x_119 = !lean_is_exclusive(x_1);
if (x_119 == 0)
{
x_102 = x_1;
x_103 = x_119;
goto block_118;
}
else
{
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_1);
x_102 = lean_box(0);
x_103 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_117; 
x_104 = l_Lean_IR_NormalizeIds_normIndex(x_99, x_2);
lean_dec(x_99);
x_105 = l_Lean_IR_NormalizeIds_normFnBody(x_101, x_2, x_3);
x_106 = lean_ctor_get(x_105, 0);
x_107 = lean_ctor_get(x_105, 1);
x_117 = !lean_is_exclusive(x_105);
if (x_117 == 0)
{
x_108 = x_105;
x_109 = x_117;
goto block_116;
}
else
{
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_105);
x_108 = lean_box(0);
x_109 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_110; 
if (x_103 == 0)
{
lean_ctor_set(x_102, 2, x_106);
lean_ctor_set(x_102, 0, x_104);
x_110 = x_102;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_115, 0, x_104);
lean_ctor_set(x_115, 1, x_100);
lean_ctor_set(x_115, 2, x_106);
x_110 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_111; 
if (x_109 == 0)
{
lean_ctor_set(x_108, 0, x_110);
x_111 = x_108;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_107);
x_111 = x_113;
goto block_112;
}
block_112:
{
return x_111;
}
}
}
}
}
case 4:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_142; 
x_120 = lean_ctor_get(x_1, 0);
x_121 = lean_ctor_get(x_1, 1);
x_122 = lean_ctor_get(x_1, 2);
x_123 = lean_ctor_get(x_1, 3);
x_142 = !lean_is_exclusive(x_1);
if (x_142 == 0)
{
x_124 = x_1;
x_125 = x_142;
goto block_141;
}
else
{
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_1);
x_124 = lean_box(0);
x_125 = x_142;
goto block_141;
}
block_141:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_140; 
x_126 = l_Lean_IR_NormalizeIds_normIndex(x_120, x_2);
lean_dec(x_120);
x_127 = l_Lean_IR_NormalizeIds_normIndex(x_122, x_2);
lean_dec(x_122);
x_128 = l_Lean_IR_NormalizeIds_normFnBody(x_123, x_2, x_3);
x_129 = lean_ctor_get(x_128, 0);
x_130 = lean_ctor_get(x_128, 1);
x_140 = !lean_is_exclusive(x_128);
if (x_140 == 0)
{
x_131 = x_128;
x_132 = x_140;
goto block_139;
}
else
{
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_128);
x_131 = lean_box(0);
x_132 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_133; 
if (x_125 == 0)
{
lean_ctor_set(x_124, 3, x_129);
lean_ctor_set(x_124, 2, x_127);
lean_ctor_set(x_124, 0, x_126);
x_133 = x_124;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_138, 0, x_126);
lean_ctor_set(x_138, 1, x_121);
lean_ctor_set(x_138, 2, x_127);
lean_ctor_set(x_138, 3, x_129);
x_133 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_134; 
if (x_132 == 0)
{
lean_ctor_set(x_131, 0, x_133);
x_134 = x_131;
goto block_135;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_130);
x_134 = x_136;
goto block_135;
}
block_135:
{
return x_134;
}
}
}
}
}
case 5:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_167; 
x_143 = lean_ctor_get(x_1, 0);
x_144 = lean_ctor_get(x_1, 1);
x_145 = lean_ctor_get(x_1, 2);
x_146 = lean_ctor_get(x_1, 3);
x_147 = lean_ctor_get(x_1, 4);
x_148 = lean_ctor_get(x_1, 5);
x_167 = !lean_is_exclusive(x_1);
if (x_167 == 0)
{
x_149 = x_1;
x_150 = x_167;
goto block_166;
}
else
{
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_1);
x_149 = lean_box(0);
x_150 = x_167;
goto block_166;
}
block_166:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; uint8_t x_165; 
x_151 = l_Lean_IR_NormalizeIds_normIndex(x_143, x_2);
lean_dec(x_143);
x_152 = l_Lean_IR_NormalizeIds_normIndex(x_146, x_2);
lean_dec(x_146);
x_153 = l_Lean_IR_NormalizeIds_normFnBody(x_148, x_2, x_3);
x_154 = lean_ctor_get(x_153, 0);
x_155 = lean_ctor_get(x_153, 1);
x_165 = !lean_is_exclusive(x_153);
if (x_165 == 0)
{
x_156 = x_153;
x_157 = x_165;
goto block_164;
}
else
{
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_153);
x_156 = lean_box(0);
x_157 = x_165;
goto block_164;
}
block_164:
{
lean_object* x_158; 
if (x_150 == 0)
{
lean_ctor_set(x_149, 5, x_154);
lean_ctor_set(x_149, 3, x_152);
lean_ctor_set(x_149, 0, x_151);
x_158 = x_149;
goto block_162;
}
else
{
lean_object* x_163; 
x_163 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_163, 0, x_151);
lean_ctor_set(x_163, 1, x_144);
lean_ctor_set(x_163, 2, x_145);
lean_ctor_set(x_163, 3, x_152);
lean_ctor_set(x_163, 4, x_147);
lean_ctor_set(x_163, 5, x_154);
x_158 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_159; 
if (x_157 == 0)
{
lean_ctor_set(x_156, 0, x_158);
x_159 = x_156;
goto block_160;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_155);
x_159 = x_161;
goto block_160;
}
block_160:
{
return x_159;
}
}
}
}
}
case 6:
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; uint8_t x_190; 
x_168 = lean_ctor_get(x_1, 0);
x_169 = lean_ctor_get(x_1, 1);
x_170 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_171 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_172 = lean_ctor_get(x_1, 2);
x_190 = !lean_is_exclusive(x_1);
if (x_190 == 0)
{
x_173 = x_1;
x_174 = x_190;
goto block_189;
}
else
{
lean_inc(x_172);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_1);
x_173 = lean_box(0);
x_174 = x_190;
goto block_189;
}
block_189:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; uint8_t x_188; 
x_175 = l_Lean_IR_NormalizeIds_normIndex(x_168, x_2);
lean_dec(x_168);
x_176 = l_Lean_IR_NormalizeIds_normFnBody(x_172, x_2, x_3);
x_177 = lean_ctor_get(x_176, 0);
x_178 = lean_ctor_get(x_176, 1);
x_188 = !lean_is_exclusive(x_176);
if (x_188 == 0)
{
x_179 = x_176;
x_180 = x_188;
goto block_187;
}
else
{
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_176);
x_179 = lean_box(0);
x_180 = x_188;
goto block_187;
}
block_187:
{
lean_object* x_181; 
if (x_174 == 0)
{
lean_ctor_set(x_173, 2, x_177);
lean_ctor_set(x_173, 0, x_175);
x_181 = x_173;
goto block_185;
}
else
{
lean_object* x_186; 
x_186 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_186, 0, x_175);
lean_ctor_set(x_186, 1, x_169);
lean_ctor_set(x_186, 2, x_177);
lean_ctor_set_uint8(x_186, sizeof(void*)*3, x_170);
lean_ctor_set_uint8(x_186, sizeof(void*)*3 + 1, x_171);
x_181 = x_186;
goto block_185;
}
block_185:
{
lean_object* x_182; 
if (x_180 == 0)
{
lean_ctor_set(x_179, 0, x_181);
x_182 = x_179;
goto block_183;
}
else
{
lean_object* x_184; 
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_178);
x_182 = x_184;
goto block_183;
}
block_183:
{
return x_182;
}
}
}
}
}
case 7:
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; uint8_t x_213; 
x_191 = lean_ctor_get(x_1, 0);
x_192 = lean_ctor_get(x_1, 1);
x_193 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_194 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_195 = lean_ctor_get(x_1, 2);
x_213 = !lean_is_exclusive(x_1);
if (x_213 == 0)
{
x_196 = x_1;
x_197 = x_213;
goto block_212;
}
else
{
lean_inc(x_195);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_1);
x_196 = lean_box(0);
x_197 = x_213;
goto block_212;
}
block_212:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; uint8_t x_211; 
x_198 = l_Lean_IR_NormalizeIds_normIndex(x_191, x_2);
lean_dec(x_191);
x_199 = l_Lean_IR_NormalizeIds_normFnBody(x_195, x_2, x_3);
x_200 = lean_ctor_get(x_199, 0);
x_201 = lean_ctor_get(x_199, 1);
x_211 = !lean_is_exclusive(x_199);
if (x_211 == 0)
{
x_202 = x_199;
x_203 = x_211;
goto block_210;
}
else
{
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_199);
x_202 = lean_box(0);
x_203 = x_211;
goto block_210;
}
block_210:
{
lean_object* x_204; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 2, x_200);
lean_ctor_set(x_196, 0, x_198);
x_204 = x_196;
goto block_208;
}
else
{
lean_object* x_209; 
x_209 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_209, 0, x_198);
lean_ctor_set(x_209, 1, x_192);
lean_ctor_set(x_209, 2, x_200);
lean_ctor_set_uint8(x_209, sizeof(void*)*3, x_193);
lean_ctor_set_uint8(x_209, sizeof(void*)*3 + 1, x_194);
x_204 = x_209;
goto block_208;
}
block_208:
{
lean_object* x_205; 
if (x_203 == 0)
{
lean_ctor_set(x_202, 0, x_204);
x_205 = x_202;
goto block_206;
}
else
{
lean_object* x_207; 
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_201);
x_205 = x_207;
goto block_206;
}
block_206:
{
return x_205;
}
}
}
}
}
case 8:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; uint8_t x_233; 
x_214 = lean_ctor_get(x_1, 0);
x_215 = lean_ctor_get(x_1, 1);
x_233 = !lean_is_exclusive(x_1);
if (x_233 == 0)
{
x_216 = x_1;
x_217 = x_233;
goto block_232;
}
else
{
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_1);
x_216 = lean_box(0);
x_217 = x_233;
goto block_232;
}
block_232:
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; uint8_t x_231; 
x_218 = l_Lean_IR_NormalizeIds_normIndex(x_214, x_2);
lean_dec(x_214);
x_219 = l_Lean_IR_NormalizeIds_normFnBody(x_215, x_2, x_3);
x_220 = lean_ctor_get(x_219, 0);
x_221 = lean_ctor_get(x_219, 1);
x_231 = !lean_is_exclusive(x_219);
if (x_231 == 0)
{
x_222 = x_219;
x_223 = x_231;
goto block_230;
}
else
{
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_219);
x_222 = lean_box(0);
x_223 = x_231;
goto block_230;
}
block_230:
{
lean_object* x_224; 
if (x_217 == 0)
{
lean_ctor_set(x_216, 1, x_220);
lean_ctor_set(x_216, 0, x_218);
x_224 = x_216;
goto block_228;
}
else
{
lean_object* x_229; 
x_229 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_229, 0, x_218);
lean_ctor_set(x_229, 1, x_220);
x_224 = x_229;
goto block_228;
}
block_228:
{
lean_object* x_225; 
if (x_223 == 0)
{
lean_ctor_set(x_222, 0, x_224);
x_225 = x_222;
goto block_226;
}
else
{
lean_object* x_227; 
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_221);
x_225 = x_227;
goto block_226;
}
block_226:
{
return x_225;
}
}
}
}
}
case 9:
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; uint8_t x_257; 
x_234 = lean_ctor_get(x_1, 0);
x_235 = lean_ctor_get(x_1, 1);
x_236 = lean_ctor_get(x_1, 2);
x_237 = lean_ctor_get(x_1, 3);
x_257 = !lean_is_exclusive(x_1);
if (x_257 == 0)
{
x_238 = x_1;
x_239 = x_257;
goto block_256;
}
else
{
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_1);
x_238 = lean_box(0);
x_239 = x_257;
goto block_256;
}
block_256:
{
lean_object* x_240; size_t x_241; size_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; uint8_t x_255; 
x_240 = l_Lean_IR_NormalizeIds_normIndex(x_235, x_2);
lean_dec(x_235);
x_241 = lean_array_size(x_237);
x_242 = 0;
x_243 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(x_241, x_242, x_237, x_2, x_3);
x_244 = lean_ctor_get(x_243, 0);
x_245 = lean_ctor_get(x_243, 1);
x_255 = !lean_is_exclusive(x_243);
if (x_255 == 0)
{
x_246 = x_243;
x_247 = x_255;
goto block_254;
}
else
{
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_243);
x_246 = lean_box(0);
x_247 = x_255;
goto block_254;
}
block_254:
{
lean_object* x_248; 
if (x_239 == 0)
{
lean_ctor_set(x_238, 3, x_244);
lean_ctor_set(x_238, 1, x_240);
x_248 = x_238;
goto block_252;
}
else
{
lean_object* x_253; 
x_253 = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(x_253, 0, x_234);
lean_ctor_set(x_253, 1, x_240);
lean_ctor_set(x_253, 2, x_236);
lean_ctor_set(x_253, 3, x_244);
x_248 = x_253;
goto block_252;
}
block_252:
{
lean_object* x_249; 
if (x_247 == 0)
{
lean_ctor_set(x_246, 0, x_248);
x_249 = x_246;
goto block_250;
}
else
{
lean_object* x_251; 
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_245);
x_249 = x_251;
goto block_250;
}
block_250:
{
return x_249;
}
}
}
}
}
case 10:
{
lean_object* x_258; lean_object* x_259; uint8_t x_260; uint8_t x_267; 
x_258 = lean_ctor_get(x_1, 0);
x_267 = !lean_is_exclusive(x_1);
if (x_267 == 0)
{
x_259 = x_1;
x_260 = x_267;
goto block_266;
}
else
{
lean_inc(x_258);
lean_dec(x_1);
x_259 = lean_box(0);
x_260 = x_267;
goto block_266;
}
block_266:
{
lean_object* x_261; lean_object* x_262; 
x_261 = l_Lean_IR_NormalizeIds_normArg(x_258, x_2);
lean_dec(x_2);
if (x_260 == 0)
{
lean_ctor_set(x_259, 0, x_261);
x_262 = x_259;
goto block_264;
}
else
{
lean_object* x_265; 
x_265 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_265, 0, x_261);
x_262 = x_265;
goto block_264;
}
block_264:
{
lean_object* x_263; 
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_3);
return x_263;
}
}
}
case 11:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; uint8_t x_279; 
x_268 = lean_ctor_get(x_1, 0);
x_269 = lean_ctor_get(x_1, 1);
x_279 = !lean_is_exclusive(x_1);
if (x_279 == 0)
{
x_270 = x_1;
x_271 = x_279;
goto block_278;
}
else
{
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_1);
x_270 = lean_box(0);
x_271 = x_279;
goto block_278;
}
block_278:
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = l_Lean_IR_NormalizeIds_normIndex(x_268, x_2);
lean_dec(x_268);
x_273 = l_Lean_IR_NormalizeIds_normArgs(x_269, x_2);
lean_dec(x_2);
if (x_271 == 0)
{
lean_ctor_set(x_270, 1, x_273);
lean_ctor_set(x_270, 0, x_272);
x_274 = x_270;
goto block_276;
}
else
{
lean_object* x_277; 
x_277 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_277, 0, x_272);
lean_ctor_set(x_277, 1, x_273);
x_274 = x_277;
goto block_276;
}
block_276:
{
lean_object* x_275; 
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_3);
return x_275;
}
}
}
default: 
{
lean_object* x_280; 
lean_dec(x_2);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_1);
lean_ctor_set(x_280, 1, x_3);
return x_280;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_3, x_2, x_9);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_29; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
x_29 = !lean_is_exclusive(x_8);
if (x_29 == 0)
{
x_20 = x_8;
x_21 = x_29;
goto block_28;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_box(0);
x_21 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_4);
x_22 = l_Lean_IR_NormalizeIds_normFnBody(x_19, x_4, x_5);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_23);
x_25 = x_20;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_23);
x_25 = x_27;
goto block_26;
}
block_26:
{
x_11 = x_25;
x_12 = x_24;
goto block_17;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_40; 
x_30 = lean_ctor_get(x_8, 0);
x_40 = !lean_is_exclusive(x_8);
if (x_40 == 0)
{
x_31 = x_8;
x_32 = x_40;
goto block_39;
}
else
{
lean_inc(x_30);
lean_dec(x_8);
x_31 = lean_box(0);
x_32 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc(x_4);
x_33 = l_Lean_IR_NormalizeIds_normFnBody(x_30, x_4, x_5);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
if (x_32 == 0)
{
lean_ctor_set(x_31, 0, x_34);
x_36 = x_31;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_34);
x_36 = x_38;
goto block_37;
}
block_37:
{
x_11 = x_36;
x_12 = x_35;
goto block_17;
}
}
}
block_17:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_10, x_2, x_11);
x_2 = x_14;
x_3 = x_15;
x_5 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_20; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 3);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_array_get_size(x_4);
x_26 = lean_nat_dec_lt(x_24, x_25);
if (x_26 == 0)
{
x_6 = x_2;
x_7 = x_3;
goto block_19;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_25, x_25);
if (x_27 == 0)
{
if (x_26 == 0)
{
x_6 = x_2;
x_7 = x_3;
goto block_19;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_25);
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(x_4, x_28, x_29, x_2, x_3);
x_20 = x_30;
goto block_23;
}
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_25);
x_33 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(x_4, x_31, x_32, x_2, x_3);
x_20 = x_33;
goto block_23;
}
}
block_19:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_18; 
lean_inc(x_5);
x_8 = l_Lean_IR_NormalizeIds_normFnBody(x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
x_10 = lean_ctor_get(x_8, 1);
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
x_11 = x_8;
x_12 = x_18;
goto block_17;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_IR_Decl_updateBody_x21(x_1, x_9);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_13);
x_14 = x_11;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_10);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_6 = x_21;
x_7 = x_22;
goto block_19;
}
}
else
{
lean_object* x_34; 
lean_dec(x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_3);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_normalizeIds(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_IR_NormalizeIds_normDecl(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_11; 
x_3 = lean_ctor_get(x_2, 0);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
x_4 = x_2;
x_5 = x_11;
goto block_10;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_1(x_1, x_3);
if (x_5 == 0)
{
lean_ctor_set(x_4, 0, x_6);
x_7 = x_4;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_6);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_dec_ref(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_15 = lean_ctor_get(x_6, 0);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
x_16 = x_6;
x_17 = x_23;
goto block_22;
}
else
{
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_18; lean_object* x_19; 
lean_inc_ref(x_1);
x_18 = lean_apply_1(x_1, x_15);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
x_9 = x_19;
goto block_14;
}
}
}
else
{
x_9 = x_6;
goto block_14;
}
block_14:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapExpr(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_12; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
x_5 = x_2;
x_6 = x_12;
goto block_11;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_IR_MapVars_mapArgs(x_1, x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_7);
x_8 = x_5;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_7);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_22 = !lean_is_exclusive(x_2);
if (x_22 == 0)
{
x_15 = x_2;
x_16 = x_22;
goto block_21;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_apply_1(x_1, x_14);
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_17);
x_18 = x_15;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
case 2:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_35; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_26 = lean_ctor_get(x_2, 2);
x_35 = !lean_is_exclusive(x_2);
if (x_35 == 0)
{
x_27 = x_2;
x_28 = x_35;
goto block_34;
}
else
{
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc_ref(x_1);
x_29 = lean_apply_1(x_1, x_23);
x_30 = l_Lean_IR_MapVars_mapArgs(x_1, x_26);
if (x_28 == 0)
{
lean_ctor_set(x_27, 2, x_30);
lean_ctor_set(x_27, 0, x_29);
x_31 = x_27;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_24);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_25);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
case 3:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_45; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_2, 1);
x_45 = !lean_is_exclusive(x_2);
if (x_45 == 0)
{
x_38 = x_2;
x_39 = x_45;
goto block_44;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_2);
x_38 = lean_box(0);
x_39 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_apply_1(x_1, x_37);
if (x_39 == 0)
{
lean_ctor_set(x_38, 1, x_40);
x_41 = x_38;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
case 4:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_55; 
x_46 = lean_ctor_get(x_2, 0);
x_47 = lean_ctor_get(x_2, 1);
x_55 = !lean_is_exclusive(x_2);
if (x_55 == 0)
{
x_48 = x_2;
x_49 = x_55;
goto block_54;
}
else
{
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_2);
x_48 = lean_box(0);
x_49 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_apply_1(x_1, x_47);
if (x_49 == 0)
{
lean_ctor_set(x_48, 1, x_50);
x_51 = x_48;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
case 5:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_66; 
x_56 = lean_ctor_get(x_2, 0);
x_57 = lean_ctor_get(x_2, 1);
x_58 = lean_ctor_get(x_2, 2);
x_66 = !lean_is_exclusive(x_2);
if (x_66 == 0)
{
x_59 = x_2;
x_60 = x_66;
goto block_65;
}
else
{
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_2);
x_59 = lean_box(0);
x_60 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_apply_1(x_1, x_58);
if (x_60 == 0)
{
lean_ctor_set(x_59, 2, x_61);
x_62 = x_59;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_64, 1, x_57);
lean_ctor_set(x_64, 2, x_61);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
case 6:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_76; 
x_67 = lean_ctor_get(x_2, 0);
x_68 = lean_ctor_get(x_2, 1);
x_76 = !lean_is_exclusive(x_2);
if (x_76 == 0)
{
x_69 = x_2;
x_70 = x_76;
goto block_75;
}
else
{
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_2);
x_69 = lean_box(0);
x_70 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Lean_IR_MapVars_mapArgs(x_1, x_68);
if (x_70 == 0)
{
lean_ctor_set(x_69, 1, x_71);
x_72 = x_69;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set(x_74, 1, x_71);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
}
case 7:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_86; 
x_77 = lean_ctor_get(x_2, 0);
x_78 = lean_ctor_get(x_2, 1);
x_86 = !lean_is_exclusive(x_2);
if (x_86 == 0)
{
x_79 = x_2;
x_80 = x_86;
goto block_85;
}
else
{
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_2);
x_79 = lean_box(0);
x_80 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_81; lean_object* x_82; 
x_81 = l_Lean_IR_MapVars_mapArgs(x_1, x_78);
if (x_80 == 0)
{
lean_ctor_set(x_79, 1, x_81);
x_82 = x_79;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_81);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
case 8:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_97; 
x_87 = lean_ctor_get(x_2, 0);
x_88 = lean_ctor_get(x_2, 1);
x_97 = !lean_is_exclusive(x_2);
if (x_97 == 0)
{
x_89 = x_2;
x_90 = x_97;
goto block_96;
}
else
{
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_2);
x_89 = lean_box(0);
x_90 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_inc_ref(x_1);
x_91 = lean_apply_1(x_1, x_87);
x_92 = l_Lean_IR_MapVars_mapArgs(x_1, x_88);
if (x_90 == 0)
{
lean_ctor_set(x_89, 1, x_92);
lean_ctor_set(x_89, 0, x_91);
x_93 = x_89;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_92);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
case 9:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_107; 
x_98 = lean_ctor_get(x_2, 0);
x_99 = lean_ctor_get(x_2, 1);
x_107 = !lean_is_exclusive(x_2);
if (x_107 == 0)
{
x_100 = x_2;
x_101 = x_107;
goto block_106;
}
else
{
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_2);
x_100 = lean_box(0);
x_101 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_apply_1(x_1, x_99);
if (x_101 == 0)
{
lean_ctor_set(x_100, 1, x_102);
x_103 = x_100;
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_105, 0, x_98);
lean_ctor_set(x_105, 1, x_102);
x_103 = x_105;
goto block_104;
}
block_104:
{
return x_103;
}
}
}
case 10:
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_116; 
x_108 = lean_ctor_get(x_2, 0);
x_116 = !lean_is_exclusive(x_2);
if (x_116 == 0)
{
x_109 = x_2;
x_110 = x_116;
goto block_115;
}
else
{
lean_inc(x_108);
lean_dec(x_2);
x_109 = lean_box(0);
x_110 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_apply_1(x_1, x_108);
if (x_110 == 0)
{
lean_ctor_set(x_109, 0, x_111);
x_112 = x_109;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_114, 0, x_111);
x_112 = x_114;
goto block_113;
}
block_113:
{
return x_112;
}
}
}
case 11:
{
lean_dec_ref(x_1);
return x_2;
}
default: 
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_125; 
x_117 = lean_ctor_get(x_2, 0);
x_125 = !lean_is_exclusive(x_2);
if (x_125 == 0)
{
x_118 = x_2;
x_119 = x_125;
goto block_124;
}
else
{
lean_inc(x_117);
lean_dec(x_2);
x_118 = lean_box(0);
x_119 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_apply_1(x_1, x_117);
if (x_119 == 0)
{
lean_ctor_set(x_118, 0, x_120);
x_121 = x_118;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_123, 0, x_120);
x_121 = x_123;
goto block_122;
}
block_122:
{
return x_121;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_15; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
x_7 = x_2;
x_8 = x_15;
goto block_14;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_1);
x_9 = l_Lean_IR_MapVars_mapExpr(x_1, x_5);
x_10 = l_Lean_IR_MapVars_mapFnBody(x_1, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 3, x_10);
lean_ctor_set(x_7, 2, x_9);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_4);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_28; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_2, 2);
x_19 = lean_ctor_get(x_2, 3);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
x_20 = x_2;
x_21 = x_28;
goto block_27;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc_ref(x_1);
x_22 = l_Lean_IR_MapVars_mapFnBody(x_1, x_18);
x_23 = l_Lean_IR_MapVars_mapFnBody(x_1, x_19);
if (x_21 == 0)
{
lean_ctor_set(x_20, 3, x_23);
lean_ctor_set(x_20, 2, x_22);
x_24 = x_20;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_17);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
case 2:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_52; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_ctor_get(x_2, 2);
x_32 = lean_ctor_get(x_2, 3);
x_52 = !lean_is_exclusive(x_2);
if (x_52 == 0)
{
x_33 = x_2;
x_34 = x_52;
goto block_51;
}
else
{
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_1);
x_35 = lean_apply_1(x_1, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_50; 
x_42 = lean_ctor_get(x_31, 0);
x_50 = !lean_is_exclusive(x_31);
if (x_50 == 0)
{
x_43 = x_31;
x_44 = x_50;
goto block_49;
}
else
{
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_box(0);
x_44 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_45; lean_object* x_46; 
lean_inc_ref(x_1);
x_45 = lean_apply_1(x_1, x_42);
if (x_44 == 0)
{
lean_ctor_set(x_43, 0, x_45);
x_46 = x_43;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
x_36 = x_46;
goto block_41;
}
}
}
else
{
x_36 = x_31;
goto block_41;
}
block_41:
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_IR_MapVars_mapFnBody(x_1, x_32);
if (x_34 == 0)
{
lean_ctor_set(x_33, 3, x_37);
lean_ctor_set(x_33, 2, x_36);
lean_ctor_set(x_33, 0, x_35);
x_38 = x_33;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_36);
lean_ctor_set(x_40, 3, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
case 3:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_64; 
x_53 = lean_ctor_get(x_2, 0);
x_54 = lean_ctor_get(x_2, 1);
x_55 = lean_ctor_get(x_2, 2);
x_64 = !lean_is_exclusive(x_2);
if (x_64 == 0)
{
x_56 = x_2;
x_57 = x_64;
goto block_63;
}
else
{
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_2);
x_56 = lean_box(0);
x_57 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_inc_ref(x_1);
x_58 = lean_apply_1(x_1, x_53);
x_59 = l_Lean_IR_MapVars_mapFnBody(x_1, x_55);
if (x_57 == 0)
{
lean_ctor_set(x_56, 2, x_59);
lean_ctor_set(x_56, 0, x_58);
x_60 = x_56;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_59);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
case 4:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_78; 
x_65 = lean_ctor_get(x_2, 0);
x_66 = lean_ctor_get(x_2, 1);
x_67 = lean_ctor_get(x_2, 2);
x_68 = lean_ctor_get(x_2, 3);
x_78 = !lean_is_exclusive(x_2);
if (x_78 == 0)
{
x_69 = x_2;
x_70 = x_78;
goto block_77;
}
else
{
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_2);
x_69 = lean_box(0);
x_70 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_inc_ref(x_1);
x_71 = lean_apply_1(x_1, x_65);
lean_inc_ref(x_1);
x_72 = lean_apply_1(x_1, x_67);
x_73 = l_Lean_IR_MapVars_mapFnBody(x_1, x_68);
if (x_70 == 0)
{
lean_ctor_set(x_69, 3, x_73);
lean_ctor_set(x_69, 2, x_72);
lean_ctor_set(x_69, 0, x_71);
x_74 = x_69;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_66);
lean_ctor_set(x_76, 2, x_72);
lean_ctor_set(x_76, 3, x_73);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
case 5:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_94; 
x_79 = lean_ctor_get(x_2, 0);
x_80 = lean_ctor_get(x_2, 1);
x_81 = lean_ctor_get(x_2, 2);
x_82 = lean_ctor_get(x_2, 3);
x_83 = lean_ctor_get(x_2, 4);
x_84 = lean_ctor_get(x_2, 5);
x_94 = !lean_is_exclusive(x_2);
if (x_94 == 0)
{
x_85 = x_2;
x_86 = x_94;
goto block_93;
}
else
{
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_2);
x_85 = lean_box(0);
x_86 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_inc_ref(x_1);
x_87 = lean_apply_1(x_1, x_79);
lean_inc_ref(x_1);
x_88 = lean_apply_1(x_1, x_82);
x_89 = l_Lean_IR_MapVars_mapFnBody(x_1, x_84);
if (x_86 == 0)
{
lean_ctor_set(x_85, 5, x_89);
lean_ctor_set(x_85, 3, x_88);
lean_ctor_set(x_85, 0, x_87);
x_90 = x_85;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_80);
lean_ctor_set(x_92, 2, x_81);
lean_ctor_set(x_92, 3, x_88);
lean_ctor_set(x_92, 4, x_83);
lean_ctor_set(x_92, 5, x_89);
x_90 = x_92;
goto block_91;
}
block_91:
{
return x_90;
}
}
}
case 6:
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_108; 
x_95 = lean_ctor_get(x_2, 0);
x_96 = lean_ctor_get(x_2, 1);
x_97 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_98 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_99 = lean_ctor_get(x_2, 2);
x_108 = !lean_is_exclusive(x_2);
if (x_108 == 0)
{
x_100 = x_2;
x_101 = x_108;
goto block_107;
}
else
{
lean_inc(x_99);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_2);
x_100 = lean_box(0);
x_101 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_inc_ref(x_1);
x_102 = lean_apply_1(x_1, x_95);
x_103 = l_Lean_IR_MapVars_mapFnBody(x_1, x_99);
if (x_101 == 0)
{
lean_ctor_set(x_100, 2, x_103);
lean_ctor_set(x_100, 0, x_102);
x_104 = x_100;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_106, 0, x_102);
lean_ctor_set(x_106, 1, x_96);
lean_ctor_set(x_106, 2, x_103);
lean_ctor_set_uint8(x_106, sizeof(void*)*3, x_97);
lean_ctor_set_uint8(x_106, sizeof(void*)*3 + 1, x_98);
x_104 = x_106;
goto block_105;
}
block_105:
{
return x_104;
}
}
}
case 7:
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_122; 
x_109 = lean_ctor_get(x_2, 0);
x_110 = lean_ctor_get(x_2, 1);
x_111 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_112 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_113 = lean_ctor_get(x_2, 2);
x_122 = !lean_is_exclusive(x_2);
if (x_122 == 0)
{
x_114 = x_2;
x_115 = x_122;
goto block_121;
}
else
{
lean_inc(x_113);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_2);
x_114 = lean_box(0);
x_115 = x_122;
goto block_121;
}
block_121:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_inc_ref(x_1);
x_116 = lean_apply_1(x_1, x_109);
x_117 = l_Lean_IR_MapVars_mapFnBody(x_1, x_113);
if (x_115 == 0)
{
lean_ctor_set(x_114, 2, x_117);
lean_ctor_set(x_114, 0, x_116);
x_118 = x_114;
goto block_119;
}
else
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_120, 0, x_116);
lean_ctor_set(x_120, 1, x_110);
lean_ctor_set(x_120, 2, x_117);
lean_ctor_set_uint8(x_120, sizeof(void*)*3, x_111);
lean_ctor_set_uint8(x_120, sizeof(void*)*3 + 1, x_112);
x_118 = x_120;
goto block_119;
}
block_119:
{
return x_118;
}
}
}
case 8:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_133; 
x_123 = lean_ctor_get(x_2, 0);
x_124 = lean_ctor_get(x_2, 1);
x_133 = !lean_is_exclusive(x_2);
if (x_133 == 0)
{
x_125 = x_2;
x_126 = x_133;
goto block_132;
}
else
{
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_2);
x_125 = lean_box(0);
x_126 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_inc_ref(x_1);
x_127 = lean_apply_1(x_1, x_123);
x_128 = l_Lean_IR_MapVars_mapFnBody(x_1, x_124);
if (x_126 == 0)
{
lean_ctor_set(x_125, 1, x_128);
lean_ctor_set(x_125, 0, x_127);
x_129 = x_125;
goto block_130;
}
else
{
lean_object* x_131; 
x_131 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_131, 0, x_127);
lean_ctor_set(x_131, 1, x_128);
x_129 = x_131;
goto block_130;
}
block_130:
{
return x_129;
}
}
}
case 9:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_148; 
x_134 = lean_ctor_get(x_2, 0);
x_135 = lean_ctor_get(x_2, 1);
x_136 = lean_ctor_get(x_2, 2);
x_137 = lean_ctor_get(x_2, 3);
x_148 = !lean_is_exclusive(x_2);
if (x_148 == 0)
{
x_138 = x_2;
x_139 = x_148;
goto block_147;
}
else
{
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_2);
x_138 = lean_box(0);
x_139 = x_148;
goto block_147;
}
block_147:
{
lean_object* x_140; size_t x_141; size_t x_142; lean_object* x_143; lean_object* x_144; 
lean_inc_ref(x_1);
x_140 = lean_apply_1(x_1, x_135);
x_141 = lean_array_size(x_137);
x_142 = 0;
x_143 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(x_1, x_141, x_142, x_137);
if (x_139 == 0)
{
lean_ctor_set(x_138, 3, x_143);
lean_ctor_set(x_138, 1, x_140);
x_144 = x_138;
goto block_145;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(x_146, 0, x_134);
lean_ctor_set(x_146, 1, x_140);
lean_ctor_set(x_146, 2, x_136);
lean_ctor_set(x_146, 3, x_143);
x_144 = x_146;
goto block_145;
}
block_145:
{
return x_144;
}
}
}
case 10:
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_2, 0);
lean_inc(x_149);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; uint8_t x_151; uint8_t x_165; 
x_165 = !lean_is_exclusive(x_2);
if (x_165 == 0)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_2, 0);
lean_dec(x_166);
x_150 = x_2;
x_151 = x_165;
goto block_164;
}
else
{
lean_dec(x_2);
x_150 = lean_box(0);
x_151 = x_165;
goto block_164;
}
block_164:
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; uint8_t x_163; 
x_152 = lean_ctor_get(x_149, 0);
x_163 = !lean_is_exclusive(x_149);
if (x_163 == 0)
{
x_153 = x_149;
x_154 = x_163;
goto block_162;
}
else
{
lean_inc(x_152);
lean_dec(x_149);
x_153 = lean_box(0);
x_154 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_apply_1(x_1, x_152);
if (x_154 == 0)
{
lean_ctor_set(x_153, 0, x_155);
x_156 = x_153;
goto block_160;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_155);
x_156 = x_161;
goto block_160;
}
block_160:
{
lean_object* x_157; 
if (x_151 == 0)
{
lean_ctor_set(x_150, 0, x_156);
x_157 = x_150;
goto block_158;
}
else
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_159, 0, x_156);
x_157 = x_159;
goto block_158;
}
block_158:
{
return x_157;
}
}
}
}
}
else
{
lean_dec_ref(x_1);
return x_2;
}
}
case 11:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; uint8_t x_176; 
x_167 = lean_ctor_get(x_2, 0);
x_168 = lean_ctor_get(x_2, 1);
x_176 = !lean_is_exclusive(x_2);
if (x_176 == 0)
{
x_169 = x_2;
x_170 = x_176;
goto block_175;
}
else
{
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_2);
x_169 = lean_box(0);
x_170 = x_176;
goto block_175;
}
block_175:
{
lean_object* x_171; lean_object* x_172; 
x_171 = l_Lean_IR_MapVars_mapArgs(x_1, x_168);
if (x_170 == 0)
{
lean_ctor_set(x_169, 1, x_171);
x_172 = x_169;
goto block_173;
}
else
{
lean_object* x_174; 
x_174 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_174, 0, x_167);
lean_ctor_set(x_174, 1, x_171);
x_172 = x_174;
goto block_173;
}
block_173:
{
return x_172;
}
}
}
default: 
{
lean_dec_ref(x_1);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_24; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
x_24 = !lean_is_exclusive(x_6);
if (x_24 == 0)
{
x_17 = x_6;
x_18 = x_24;
goto block_23;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_box(0);
x_18 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_19; lean_object* x_20; 
lean_inc_ref(x_1);
x_19 = l_Lean_IR_MapVars_mapFnBody(x_1, x_16);
if (x_18 == 0)
{
lean_ctor_set(x_17, 1, x_19);
x_20 = x_17;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
x_9 = x_20;
goto block_14;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_33; 
x_25 = lean_ctor_get(x_6, 0);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
x_26 = x_6;
x_27 = x_33;
goto block_32;
}
else
{
lean_inc(x_25);
lean_dec(x_6);
x_26 = lean_box(0);
x_27 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_28; lean_object* x_29; 
lean_inc_ref(x_1);
x_28 = l_Lean_IR_MapVars_mapFnBody(x_1, x_25);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_28);
x_29 = x_26;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
x_9 = x_29;
goto block_14;
}
}
}
block_14:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_mapVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_MapVars_mapFnBody(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_IR_instBEqVarId_beq(x_1, x_3);
if (x_4 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_FnBody_replaceVar___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_IR_FnBody_replaceVar___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Lean_IR_MapVars_mapFnBody(x_4, x_3);
return x_5;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_NormIds(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_IR_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_IR_NormIds(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_NormIds(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_NormIds(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_IR_NormIds(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_IR_NormIds(builtin);
}
#ifdef __cplusplus
}
#endif
