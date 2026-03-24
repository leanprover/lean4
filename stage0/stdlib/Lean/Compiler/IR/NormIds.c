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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_IR_Alt_body(lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_instBEqVarId_beq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkId(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkFnBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(lean_object*, size_t, size_t, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normExpr___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_NormalizeIds_withVar___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_NormalizeIds_withVar___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_NormalizeIds_withVar___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_NormalizeIds_withVar___redArg___closed__0 = (const lean_object*)&l_Lean_IR_NormalizeIds_withVar___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__0 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__0_value;
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__1 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__1_value;
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__2 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__2_value;
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__3 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__3_value;
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__4 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__4_value;
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__5 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__5_value;
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__6 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__6_value;
static const lean_ctor_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__0_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__1_value)}};
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__7 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__7_value;
static const lean_ctor_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__7_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__2_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__3_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__4_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__5_value)}};
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__8 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__8_value;
static const lean_ctor_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__8_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__6_value)}};
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__9 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value;
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__10 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__10_value;
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__4, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__11 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__11_value;
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__7, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__12 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__12_value;
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__9, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__13 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__13_value;
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_map, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__14 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__14_value;
static const lean_ctor_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__14_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__10_value)}};
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__15 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__15_value;
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_pure, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__16 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__16_value;
static const lean_ctor_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__15_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__16_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__11_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__12_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__13_value)}};
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__17 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__17_value;
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_bind, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__9_value)} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__18 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__18_value;
static const lean_ctor_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__17_value),((lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__18_value)}};
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__19 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__19_value;
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_NormalizeIds_withParams___redArg___lam__2, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withVar___redArg___closed__0_value)} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__20 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__20_value;
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
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___redArg(lean_object* v_k_1_, lean_object* v_t_2_){
_start:
{
if (lean_obj_tag(v_t_2_) == 0)
{
lean_object* v_k_3_; lean_object* v_l_4_; lean_object* v_r_5_; uint8_t v___x_6_; 
v_k_3_ = lean_ctor_get(v_t_2_, 1);
v_l_4_ = lean_ctor_get(v_t_2_, 3);
v_r_5_ = lean_ctor_get(v_t_2_, 4);
v___x_6_ = lean_nat_dec_lt(v_k_1_, v_k_3_);
if (v___x_6_ == 0)
{
uint8_t v___x_7_; 
v___x_7_ = lean_nat_dec_eq(v_k_1_, v_k_3_);
if (v___x_7_ == 0)
{
v_t_2_ = v_r_5_;
goto _start;
}
else
{
return v___x_7_;
}
}
else
{
v_t_2_ = v_l_4_;
goto _start;
}
}
else
{
uint8_t v___x_10_; 
v___x_10_ = 0;
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___redArg___boxed(lean_object* v_k_11_, lean_object* v_t_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___redArg(v_k_11_, v_t_12_);
lean_dec(v_t_12_);
lean_dec(v_k_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(lean_object* v_k_15_, lean_object* v_v_16_, lean_object* v_t_17_){
_start:
{
if (lean_obj_tag(v_t_17_) == 0)
{
lean_object* v_size_18_; lean_object* v_k_19_; lean_object* v_v_20_; lean_object* v_l_21_; lean_object* v_r_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_303_; 
v_size_18_ = lean_ctor_get(v_t_17_, 0);
v_k_19_ = lean_ctor_get(v_t_17_, 1);
v_v_20_ = lean_ctor_get(v_t_17_, 2);
v_l_21_ = lean_ctor_get(v_t_17_, 3);
v_r_22_ = lean_ctor_get(v_t_17_, 4);
v_isSharedCheck_303_ = !lean_is_exclusive(v_t_17_);
if (v_isSharedCheck_303_ == 0)
{
v___x_24_ = v_t_17_;
v_isShared_25_ = v_isSharedCheck_303_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_r_22_);
lean_inc(v_l_21_);
lean_inc(v_v_20_);
lean_inc(v_k_19_);
lean_inc(v_size_18_);
lean_dec(v_t_17_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_303_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
uint8_t v___x_26_; 
v___x_26_ = lean_nat_dec_lt(v_k_15_, v_k_19_);
if (v___x_26_ == 0)
{
uint8_t v___x_27_; 
v___x_27_ = lean_nat_dec_eq(v_k_15_, v_k_19_);
if (v___x_27_ == 0)
{
lean_object* v_impl_28_; lean_object* v___x_29_; 
lean_dec(v_size_18_);
v_impl_28_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_k_15_, v_v_16_, v_r_22_);
v___x_29_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_21_) == 0)
{
lean_object* v_size_30_; lean_object* v_size_31_; lean_object* v_k_32_; lean_object* v_v_33_; lean_object* v_l_34_; lean_object* v_r_35_; lean_object* v___x_36_; lean_object* v___x_37_; uint8_t v___x_38_; 
v_size_30_ = lean_ctor_get(v_l_21_, 0);
v_size_31_ = lean_ctor_get(v_impl_28_, 0);
lean_inc(v_size_31_);
v_k_32_ = lean_ctor_get(v_impl_28_, 1);
lean_inc(v_k_32_);
v_v_33_ = lean_ctor_get(v_impl_28_, 2);
lean_inc(v_v_33_);
v_l_34_ = lean_ctor_get(v_impl_28_, 3);
lean_inc(v_l_34_);
v_r_35_ = lean_ctor_get(v_impl_28_, 4);
lean_inc(v_r_35_);
v___x_36_ = lean_unsigned_to_nat(3u);
v___x_37_ = lean_nat_mul(v___x_36_, v_size_30_);
v___x_38_ = lean_nat_dec_lt(v___x_37_, v_size_31_);
lean_dec(v___x_37_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_42_; 
lean_dec(v_r_35_);
lean_dec(v_l_34_);
lean_dec(v_v_33_);
lean_dec(v_k_32_);
v___x_39_ = lean_nat_add(v___x_29_, v_size_30_);
v___x_40_ = lean_nat_add(v___x_39_, v_size_31_);
lean_dec(v_size_31_);
lean_dec(v___x_39_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 4, v_impl_28_);
lean_ctor_set(v___x_24_, 0, v___x_40_);
v___x_42_ = v___x_24_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_40_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v_k_19_);
lean_ctor_set(v_reuseFailAlloc_43_, 2, v_v_20_);
lean_ctor_set(v_reuseFailAlloc_43_, 3, v_l_21_);
lean_ctor_set(v_reuseFailAlloc_43_, 4, v_impl_28_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
else
{
lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_107_; 
v_isSharedCheck_107_ = !lean_is_exclusive(v_impl_28_);
if (v_isSharedCheck_107_ == 0)
{
lean_object* v_unused_108_; lean_object* v_unused_109_; lean_object* v_unused_110_; lean_object* v_unused_111_; lean_object* v_unused_112_; 
v_unused_108_ = lean_ctor_get(v_impl_28_, 4);
lean_dec(v_unused_108_);
v_unused_109_ = lean_ctor_get(v_impl_28_, 3);
lean_dec(v_unused_109_);
v_unused_110_ = lean_ctor_get(v_impl_28_, 2);
lean_dec(v_unused_110_);
v_unused_111_ = lean_ctor_get(v_impl_28_, 1);
lean_dec(v_unused_111_);
v_unused_112_ = lean_ctor_get(v_impl_28_, 0);
lean_dec(v_unused_112_);
v___x_45_ = v_impl_28_;
v_isShared_46_ = v_isSharedCheck_107_;
goto v_resetjp_44_;
}
else
{
lean_dec(v_impl_28_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_107_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v_size_47_; lean_object* v_k_48_; lean_object* v_v_49_; lean_object* v_l_50_; lean_object* v_r_51_; lean_object* v_size_52_; lean_object* v___x_53_; lean_object* v___x_54_; uint8_t v___x_55_; 
v_size_47_ = lean_ctor_get(v_l_34_, 0);
v_k_48_ = lean_ctor_get(v_l_34_, 1);
v_v_49_ = lean_ctor_get(v_l_34_, 2);
v_l_50_ = lean_ctor_get(v_l_34_, 3);
v_r_51_ = lean_ctor_get(v_l_34_, 4);
v_size_52_ = lean_ctor_get(v_r_35_, 0);
v___x_53_ = lean_unsigned_to_nat(2u);
v___x_54_ = lean_nat_mul(v___x_53_, v_size_52_);
v___x_55_ = lean_nat_dec_lt(v_size_47_, v___x_54_);
lean_dec(v___x_54_);
if (v___x_55_ == 0)
{
lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_83_; 
lean_inc(v_r_51_);
lean_inc(v_l_50_);
lean_inc(v_v_49_);
lean_inc(v_k_48_);
v_isSharedCheck_83_ = !lean_is_exclusive(v_l_34_);
if (v_isSharedCheck_83_ == 0)
{
lean_object* v_unused_84_; lean_object* v_unused_85_; lean_object* v_unused_86_; lean_object* v_unused_87_; lean_object* v_unused_88_; 
v_unused_84_ = lean_ctor_get(v_l_34_, 4);
lean_dec(v_unused_84_);
v_unused_85_ = lean_ctor_get(v_l_34_, 3);
lean_dec(v_unused_85_);
v_unused_86_ = lean_ctor_get(v_l_34_, 2);
lean_dec(v_unused_86_);
v_unused_87_ = lean_ctor_get(v_l_34_, 1);
lean_dec(v_unused_87_);
v_unused_88_ = lean_ctor_get(v_l_34_, 0);
lean_dec(v_unused_88_);
v___x_57_ = v_l_34_;
v_isShared_58_ = v_isSharedCheck_83_;
goto v_resetjp_56_;
}
else
{
lean_dec(v_l_34_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_83_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___y_62_; lean_object* v___y_63_; lean_object* v___y_64_; lean_object* v___y_73_; 
v___x_59_ = lean_nat_add(v___x_29_, v_size_30_);
v___x_60_ = lean_nat_add(v___x_59_, v_size_31_);
lean_dec(v_size_31_);
if (lean_obj_tag(v_l_50_) == 0)
{
lean_object* v_size_81_; 
v_size_81_ = lean_ctor_get(v_l_50_, 0);
lean_inc(v_size_81_);
v___y_73_ = v_size_81_;
goto v___jp_72_;
}
else
{
lean_object* v___x_82_; 
v___x_82_ = lean_unsigned_to_nat(0u);
v___y_73_ = v___x_82_;
goto v___jp_72_;
}
v___jp_61_:
{
lean_object* v___x_65_; lean_object* v___x_67_; 
v___x_65_ = lean_nat_add(v___y_63_, v___y_64_);
lean_dec(v___y_64_);
lean_dec(v___y_63_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v_r_35_);
lean_ctor_set(v___x_57_, 3, v_r_51_);
lean_ctor_set(v___x_57_, 2, v_v_33_);
lean_ctor_set(v___x_57_, 1, v_k_32_);
lean_ctor_set(v___x_57_, 0, v___x_65_);
v___x_67_ = v___x_57_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_65_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v_k_32_);
lean_ctor_set(v_reuseFailAlloc_71_, 2, v_v_33_);
lean_ctor_set(v_reuseFailAlloc_71_, 3, v_r_51_);
lean_ctor_set(v_reuseFailAlloc_71_, 4, v_r_35_);
v___x_67_ = v_reuseFailAlloc_71_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
lean_object* v___x_69_; 
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 4, v___x_67_);
lean_ctor_set(v___x_45_, 3, v___y_62_);
lean_ctor_set(v___x_45_, 2, v_v_49_);
lean_ctor_set(v___x_45_, 1, v_k_48_);
lean_ctor_set(v___x_45_, 0, v___x_60_);
v___x_69_ = v___x_45_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_70_, 1, v_k_48_);
lean_ctor_set(v_reuseFailAlloc_70_, 2, v_v_49_);
lean_ctor_set(v_reuseFailAlloc_70_, 3, v___y_62_);
lean_ctor_set(v_reuseFailAlloc_70_, 4, v___x_67_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
v___jp_72_:
{
lean_object* v___x_74_; lean_object* v___x_76_; 
v___x_74_ = lean_nat_add(v___x_59_, v___y_73_);
lean_dec(v___y_73_);
lean_dec(v___x_59_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 4, v_l_50_);
lean_ctor_set(v___x_24_, 0, v___x_74_);
v___x_76_ = v___x_24_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_74_);
lean_ctor_set(v_reuseFailAlloc_80_, 1, v_k_19_);
lean_ctor_set(v_reuseFailAlloc_80_, 2, v_v_20_);
lean_ctor_set(v_reuseFailAlloc_80_, 3, v_l_21_);
lean_ctor_set(v_reuseFailAlloc_80_, 4, v_l_50_);
v___x_76_ = v_reuseFailAlloc_80_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
lean_object* v___x_77_; 
v___x_77_ = lean_nat_add(v___x_29_, v_size_52_);
if (lean_obj_tag(v_r_51_) == 0)
{
lean_object* v_size_78_; 
v_size_78_ = lean_ctor_get(v_r_51_, 0);
lean_inc(v_size_78_);
v___y_62_ = v___x_76_;
v___y_63_ = v___x_77_;
v___y_64_ = v_size_78_;
goto v___jp_61_;
}
else
{
lean_object* v___x_79_; 
v___x_79_ = lean_unsigned_to_nat(0u);
v___y_62_ = v___x_76_;
v___y_63_ = v___x_77_;
v___y_64_ = v___x_79_;
goto v___jp_61_;
}
}
}
}
}
else
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
lean_del_object(v___x_24_);
v___x_89_ = lean_nat_add(v___x_29_, v_size_30_);
v___x_90_ = lean_nat_add(v___x_89_, v_size_31_);
lean_dec(v_size_31_);
v___x_91_ = lean_nat_add(v___x_89_, v_size_47_);
lean_dec(v___x_89_);
lean_inc_ref(v_l_21_);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 4, v_l_34_);
lean_ctor_set(v___x_45_, 3, v_l_21_);
lean_ctor_set(v___x_45_, 2, v_v_20_);
lean_ctor_set(v___x_45_, 1, v_k_19_);
lean_ctor_set(v___x_45_, 0, v___x_91_);
v___x_93_ = v___x_45_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_91_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_k_19_);
lean_ctor_set(v_reuseFailAlloc_106_, 2, v_v_20_);
lean_ctor_set(v_reuseFailAlloc_106_, 3, v_l_21_);
lean_ctor_set(v_reuseFailAlloc_106_, 4, v_l_34_);
v___x_93_ = v_reuseFailAlloc_106_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
v_isSharedCheck_100_ = !lean_is_exclusive(v_l_21_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; lean_object* v_unused_102_; lean_object* v_unused_103_; lean_object* v_unused_104_; lean_object* v_unused_105_; 
v_unused_101_ = lean_ctor_get(v_l_21_, 4);
lean_dec(v_unused_101_);
v_unused_102_ = lean_ctor_get(v_l_21_, 3);
lean_dec(v_unused_102_);
v_unused_103_ = lean_ctor_get(v_l_21_, 2);
lean_dec(v_unused_103_);
v_unused_104_ = lean_ctor_get(v_l_21_, 1);
lean_dec(v_unused_104_);
v_unused_105_ = lean_ctor_get(v_l_21_, 0);
lean_dec(v_unused_105_);
v___x_95_ = v_l_21_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_dec(v_l_21_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 4, v_r_35_);
lean_ctor_set(v___x_95_, 3, v___x_93_);
lean_ctor_set(v___x_95_, 2, v_v_33_);
lean_ctor_set(v___x_95_, 1, v_k_32_);
lean_ctor_set(v___x_95_, 0, v___x_90_);
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_90_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_k_32_);
lean_ctor_set(v_reuseFailAlloc_99_, 2, v_v_33_);
lean_ctor_set(v_reuseFailAlloc_99_, 3, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_99_, 4, v_r_35_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_113_; 
v_l_113_ = lean_ctor_get(v_impl_28_, 3);
lean_inc(v_l_113_);
if (lean_obj_tag(v_l_113_) == 0)
{
lean_object* v_r_114_; lean_object* v_k_115_; lean_object* v_v_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_139_; 
v_r_114_ = lean_ctor_get(v_impl_28_, 4);
v_k_115_ = lean_ctor_get(v_impl_28_, 1);
v_v_116_ = lean_ctor_get(v_impl_28_, 2);
v_isSharedCheck_139_ = !lean_is_exclusive(v_impl_28_);
if (v_isSharedCheck_139_ == 0)
{
lean_object* v_unused_140_; lean_object* v_unused_141_; 
v_unused_140_ = lean_ctor_get(v_impl_28_, 3);
lean_dec(v_unused_140_);
v_unused_141_ = lean_ctor_get(v_impl_28_, 0);
lean_dec(v_unused_141_);
v___x_118_ = v_impl_28_;
v_isShared_119_ = v_isSharedCheck_139_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_r_114_);
lean_inc(v_v_116_);
lean_inc(v_k_115_);
lean_dec(v_impl_28_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_139_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v_k_120_; lean_object* v_v_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_135_; 
v_k_120_ = lean_ctor_get(v_l_113_, 1);
v_v_121_ = lean_ctor_get(v_l_113_, 2);
v_isSharedCheck_135_ = !lean_is_exclusive(v_l_113_);
if (v_isSharedCheck_135_ == 0)
{
lean_object* v_unused_136_; lean_object* v_unused_137_; lean_object* v_unused_138_; 
v_unused_136_ = lean_ctor_get(v_l_113_, 4);
lean_dec(v_unused_136_);
v_unused_137_ = lean_ctor_get(v_l_113_, 3);
lean_dec(v_unused_137_);
v_unused_138_ = lean_ctor_get(v_l_113_, 0);
lean_dec(v_unused_138_);
v___x_123_ = v_l_113_;
v_isShared_124_ = v_isSharedCheck_135_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_v_121_);
lean_inc(v_k_120_);
lean_dec(v_l_113_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_135_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_125_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_114_, 2);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 4, v_r_114_);
lean_ctor_set(v___x_123_, 3, v_r_114_);
lean_ctor_set(v___x_123_, 2, v_v_20_);
lean_ctor_set(v___x_123_, 1, v_k_19_);
lean_ctor_set(v___x_123_, 0, v___x_29_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_29_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_k_19_);
lean_ctor_set(v_reuseFailAlloc_134_, 2, v_v_20_);
lean_ctor_set(v_reuseFailAlloc_134_, 3, v_r_114_);
lean_ctor_set(v_reuseFailAlloc_134_, 4, v_r_114_);
v___x_127_ = v_reuseFailAlloc_134_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_129_; 
lean_inc(v_r_114_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 3, v_r_114_);
lean_ctor_set(v___x_118_, 0, v___x_29_);
v___x_129_ = v___x_118_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_29_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_k_115_);
lean_ctor_set(v_reuseFailAlloc_133_, 2, v_v_116_);
lean_ctor_set(v_reuseFailAlloc_133_, 3, v_r_114_);
lean_ctor_set(v_reuseFailAlloc_133_, 4, v_r_114_);
v___x_129_ = v_reuseFailAlloc_133_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_131_; 
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 4, v___x_129_);
lean_ctor_set(v___x_24_, 3, v___x_127_);
lean_ctor_set(v___x_24_, 2, v_v_121_);
lean_ctor_set(v___x_24_, 1, v_k_120_);
lean_ctor_set(v___x_24_, 0, v___x_125_);
v___x_131_ = v___x_24_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_k_120_);
lean_ctor_set(v_reuseFailAlloc_132_, 2, v_v_121_);
lean_ctor_set(v_reuseFailAlloc_132_, 3, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_132_, 4, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
}
}
else
{
lean_object* v_r_142_; 
v_r_142_ = lean_ctor_get(v_impl_28_, 4);
lean_inc(v_r_142_);
if (lean_obj_tag(v_r_142_) == 0)
{
lean_object* v_k_143_; lean_object* v_v_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_155_; 
v_k_143_ = lean_ctor_get(v_impl_28_, 1);
v_v_144_ = lean_ctor_get(v_impl_28_, 2);
v_isSharedCheck_155_ = !lean_is_exclusive(v_impl_28_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; lean_object* v_unused_157_; lean_object* v_unused_158_; 
v_unused_156_ = lean_ctor_get(v_impl_28_, 4);
lean_dec(v_unused_156_);
v_unused_157_ = lean_ctor_get(v_impl_28_, 3);
lean_dec(v_unused_157_);
v_unused_158_ = lean_ctor_get(v_impl_28_, 0);
lean_dec(v_unused_158_);
v___x_146_ = v_impl_28_;
v_isShared_147_ = v_isSharedCheck_155_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_v_144_);
lean_inc(v_k_143_);
lean_dec(v_impl_28_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_155_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_148_ = lean_unsigned_to_nat(3u);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 4, v_l_113_);
lean_ctor_set(v___x_146_, 2, v_v_20_);
lean_ctor_set(v___x_146_, 1, v_k_19_);
lean_ctor_set(v___x_146_, 0, v___x_29_);
v___x_150_ = v___x_146_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_29_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_k_19_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v_v_20_);
lean_ctor_set(v_reuseFailAlloc_154_, 3, v_l_113_);
lean_ctor_set(v_reuseFailAlloc_154_, 4, v_l_113_);
v___x_150_ = v_reuseFailAlloc_154_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_152_; 
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 4, v_r_142_);
lean_ctor_set(v___x_24_, 3, v___x_150_);
lean_ctor_set(v___x_24_, 2, v_v_144_);
lean_ctor_set(v___x_24_, 1, v_k_143_);
lean_ctor_set(v___x_24_, 0, v___x_148_);
v___x_152_ = v___x_24_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_148_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_k_143_);
lean_ctor_set(v_reuseFailAlloc_153_, 2, v_v_144_);
lean_ctor_set(v_reuseFailAlloc_153_, 3, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_153_, 4, v_r_142_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
else
{
lean_object* v___x_159_; lean_object* v___x_161_; 
v___x_159_ = lean_unsigned_to_nat(2u);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 4, v_impl_28_);
lean_ctor_set(v___x_24_, 3, v_r_142_);
lean_ctor_set(v___x_24_, 0, v___x_159_);
v___x_161_ = v___x_24_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_159_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_k_19_);
lean_ctor_set(v_reuseFailAlloc_162_, 2, v_v_20_);
lean_ctor_set(v_reuseFailAlloc_162_, 3, v_r_142_);
lean_ctor_set(v_reuseFailAlloc_162_, 4, v_impl_28_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
}
else
{
lean_object* v___x_164_; 
lean_dec(v_v_20_);
lean_dec(v_k_19_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 2, v_v_16_);
lean_ctor_set(v___x_24_, 1, v_k_15_);
v___x_164_ = v___x_24_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_size_18_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_k_15_);
lean_ctor_set(v_reuseFailAlloc_165_, 2, v_v_16_);
lean_ctor_set(v_reuseFailAlloc_165_, 3, v_l_21_);
lean_ctor_set(v_reuseFailAlloc_165_, 4, v_r_22_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
else
{
lean_object* v_impl_166_; lean_object* v___x_167_; 
lean_dec(v_size_18_);
v_impl_166_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_k_15_, v_v_16_, v_l_21_);
v___x_167_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_22_) == 0)
{
lean_object* v_size_168_; lean_object* v_size_169_; lean_object* v_k_170_; lean_object* v_v_171_; lean_object* v_l_172_; lean_object* v_r_173_; lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v_size_168_ = lean_ctor_get(v_r_22_, 0);
v_size_169_ = lean_ctor_get(v_impl_166_, 0);
lean_inc(v_size_169_);
v_k_170_ = lean_ctor_get(v_impl_166_, 1);
lean_inc(v_k_170_);
v_v_171_ = lean_ctor_get(v_impl_166_, 2);
lean_inc(v_v_171_);
v_l_172_ = lean_ctor_get(v_impl_166_, 3);
lean_inc(v_l_172_);
v_r_173_ = lean_ctor_get(v_impl_166_, 4);
lean_inc(v_r_173_);
v___x_174_ = lean_unsigned_to_nat(3u);
v___x_175_ = lean_nat_mul(v___x_174_, v_size_168_);
v___x_176_ = lean_nat_dec_lt(v___x_175_, v_size_169_);
lean_dec(v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
lean_dec(v_r_173_);
lean_dec(v_l_172_);
lean_dec(v_v_171_);
lean_dec(v_k_170_);
v___x_177_ = lean_nat_add(v___x_167_, v_size_169_);
lean_dec(v_size_169_);
v___x_178_ = lean_nat_add(v___x_177_, v_size_168_);
lean_dec(v___x_177_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 3, v_impl_166_);
lean_ctor_set(v___x_24_, 0, v___x_178_);
v___x_180_ = v___x_24_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_k_19_);
lean_ctor_set(v_reuseFailAlloc_181_, 2, v_v_20_);
lean_ctor_set(v_reuseFailAlloc_181_, 3, v_impl_166_);
lean_ctor_set(v_reuseFailAlloc_181_, 4, v_r_22_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
else
{
lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_247_; 
v_isSharedCheck_247_ = !lean_is_exclusive(v_impl_166_);
if (v_isSharedCheck_247_ == 0)
{
lean_object* v_unused_248_; lean_object* v_unused_249_; lean_object* v_unused_250_; lean_object* v_unused_251_; lean_object* v_unused_252_; 
v_unused_248_ = lean_ctor_get(v_impl_166_, 4);
lean_dec(v_unused_248_);
v_unused_249_ = lean_ctor_get(v_impl_166_, 3);
lean_dec(v_unused_249_);
v_unused_250_ = lean_ctor_get(v_impl_166_, 2);
lean_dec(v_unused_250_);
v_unused_251_ = lean_ctor_get(v_impl_166_, 1);
lean_dec(v_unused_251_);
v_unused_252_ = lean_ctor_get(v_impl_166_, 0);
lean_dec(v_unused_252_);
v___x_183_ = v_impl_166_;
v_isShared_184_ = v_isSharedCheck_247_;
goto v_resetjp_182_;
}
else
{
lean_dec(v_impl_166_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_247_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v_size_185_; lean_object* v_size_186_; lean_object* v_k_187_; lean_object* v_v_188_; lean_object* v_l_189_; lean_object* v_r_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v_size_185_ = lean_ctor_get(v_l_172_, 0);
v_size_186_ = lean_ctor_get(v_r_173_, 0);
v_k_187_ = lean_ctor_get(v_r_173_, 1);
v_v_188_ = lean_ctor_get(v_r_173_, 2);
v_l_189_ = lean_ctor_get(v_r_173_, 3);
v_r_190_ = lean_ctor_get(v_r_173_, 4);
v___x_191_ = lean_unsigned_to_nat(2u);
v___x_192_ = lean_nat_mul(v___x_191_, v_size_185_);
v___x_193_ = lean_nat_dec_lt(v_size_186_, v___x_192_);
lean_dec(v___x_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_222_; 
lean_inc(v_r_190_);
lean_inc(v_l_189_);
lean_inc(v_v_188_);
lean_inc(v_k_187_);
v_isSharedCheck_222_ = !lean_is_exclusive(v_r_173_);
if (v_isSharedCheck_222_ == 0)
{
lean_object* v_unused_223_; lean_object* v_unused_224_; lean_object* v_unused_225_; lean_object* v_unused_226_; lean_object* v_unused_227_; 
v_unused_223_ = lean_ctor_get(v_r_173_, 4);
lean_dec(v_unused_223_);
v_unused_224_ = lean_ctor_get(v_r_173_, 3);
lean_dec(v_unused_224_);
v_unused_225_ = lean_ctor_get(v_r_173_, 2);
lean_dec(v_unused_225_);
v_unused_226_ = lean_ctor_get(v_r_173_, 1);
lean_dec(v_unused_226_);
v_unused_227_ = lean_ctor_get(v_r_173_, 0);
lean_dec(v_unused_227_);
v___x_195_ = v_r_173_;
v_isShared_196_ = v_isSharedCheck_222_;
goto v_resetjp_194_;
}
else
{
lean_dec(v_r_173_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_222_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___y_200_; lean_object* v___y_201_; lean_object* v___y_202_; lean_object* v___x_210_; lean_object* v___y_212_; 
v___x_197_ = lean_nat_add(v___x_167_, v_size_169_);
lean_dec(v_size_169_);
v___x_198_ = lean_nat_add(v___x_197_, v_size_168_);
lean_dec(v___x_197_);
v___x_210_ = lean_nat_add(v___x_167_, v_size_185_);
if (lean_obj_tag(v_l_189_) == 0)
{
lean_object* v_size_220_; 
v_size_220_ = lean_ctor_get(v_l_189_, 0);
lean_inc(v_size_220_);
v___y_212_ = v_size_220_;
goto v___jp_211_;
}
else
{
lean_object* v___x_221_; 
v___x_221_ = lean_unsigned_to_nat(0u);
v___y_212_ = v___x_221_;
goto v___jp_211_;
}
v___jp_199_:
{
lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_203_ = lean_nat_add(v___y_200_, v___y_202_);
lean_dec(v___y_202_);
lean_dec(v___y_200_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 4, v_r_22_);
lean_ctor_set(v___x_195_, 3, v_r_190_);
lean_ctor_set(v___x_195_, 2, v_v_20_);
lean_ctor_set(v___x_195_, 1, v_k_19_);
lean_ctor_set(v___x_195_, 0, v___x_203_);
v___x_205_ = v___x_195_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_k_19_);
lean_ctor_set(v_reuseFailAlloc_209_, 2, v_v_20_);
lean_ctor_set(v_reuseFailAlloc_209_, 3, v_r_190_);
lean_ctor_set(v_reuseFailAlloc_209_, 4, v_r_22_);
v___x_205_ = v_reuseFailAlloc_209_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_207_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 4, v___x_205_);
lean_ctor_set(v___x_183_, 3, v___y_201_);
lean_ctor_set(v___x_183_, 2, v_v_188_);
lean_ctor_set(v___x_183_, 1, v_k_187_);
lean_ctor_set(v___x_183_, 0, v___x_198_);
v___x_207_ = v___x_183_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_k_187_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v_v_188_);
lean_ctor_set(v_reuseFailAlloc_208_, 3, v___y_201_);
lean_ctor_set(v_reuseFailAlloc_208_, 4, v___x_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
v___jp_211_:
{
lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_213_ = lean_nat_add(v___x_210_, v___y_212_);
lean_dec(v___y_212_);
lean_dec(v___x_210_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 4, v_l_189_);
lean_ctor_set(v___x_24_, 3, v_l_172_);
lean_ctor_set(v___x_24_, 2, v_v_171_);
lean_ctor_set(v___x_24_, 1, v_k_170_);
lean_ctor_set(v___x_24_, 0, v___x_213_);
v___x_215_ = v___x_24_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_k_170_);
lean_ctor_set(v_reuseFailAlloc_219_, 2, v_v_171_);
lean_ctor_set(v_reuseFailAlloc_219_, 3, v_l_172_);
lean_ctor_set(v_reuseFailAlloc_219_, 4, v_l_189_);
v___x_215_ = v_reuseFailAlloc_219_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_216_; 
v___x_216_ = lean_nat_add(v___x_167_, v_size_168_);
if (lean_obj_tag(v_r_190_) == 0)
{
lean_object* v_size_217_; 
v_size_217_ = lean_ctor_get(v_r_190_, 0);
lean_inc(v_size_217_);
v___y_200_ = v___x_216_;
v___y_201_ = v___x_215_;
v___y_202_ = v_size_217_;
goto v___jp_199_;
}
else
{
lean_object* v___x_218_; 
v___x_218_ = lean_unsigned_to_nat(0u);
v___y_200_ = v___x_216_;
v___y_201_ = v___x_215_;
v___y_202_ = v___x_218_;
goto v___jp_199_;
}
}
}
}
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
lean_del_object(v___x_24_);
v___x_228_ = lean_nat_add(v___x_167_, v_size_169_);
lean_dec(v_size_169_);
v___x_229_ = lean_nat_add(v___x_228_, v_size_168_);
lean_dec(v___x_228_);
v___x_230_ = lean_nat_add(v___x_167_, v_size_168_);
v___x_231_ = lean_nat_add(v___x_230_, v_size_186_);
lean_dec(v___x_230_);
lean_inc_ref(v_r_22_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 4, v_r_22_);
lean_ctor_set(v___x_183_, 3, v_r_173_);
lean_ctor_set(v___x_183_, 2, v_v_20_);
lean_ctor_set(v___x_183_, 1, v_k_19_);
lean_ctor_set(v___x_183_, 0, v___x_231_);
v___x_233_ = v___x_183_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_k_19_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v_v_20_);
lean_ctor_set(v_reuseFailAlloc_246_, 3, v_r_173_);
lean_ctor_set(v_reuseFailAlloc_246_, 4, v_r_22_);
v___x_233_ = v_reuseFailAlloc_246_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
v_isSharedCheck_240_ = !lean_is_exclusive(v_r_22_);
if (v_isSharedCheck_240_ == 0)
{
lean_object* v_unused_241_; lean_object* v_unused_242_; lean_object* v_unused_243_; lean_object* v_unused_244_; lean_object* v_unused_245_; 
v_unused_241_ = lean_ctor_get(v_r_22_, 4);
lean_dec(v_unused_241_);
v_unused_242_ = lean_ctor_get(v_r_22_, 3);
lean_dec(v_unused_242_);
v_unused_243_ = lean_ctor_get(v_r_22_, 2);
lean_dec(v_unused_243_);
v_unused_244_ = lean_ctor_get(v_r_22_, 1);
lean_dec(v_unused_244_);
v_unused_245_ = lean_ctor_get(v_r_22_, 0);
lean_dec(v_unused_245_);
v___x_235_ = v_r_22_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_dec(v_r_22_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 4, v___x_233_);
lean_ctor_set(v___x_235_, 3, v_l_172_);
lean_ctor_set(v___x_235_, 2, v_v_171_);
lean_ctor_set(v___x_235_, 1, v_k_170_);
lean_ctor_set(v___x_235_, 0, v___x_229_);
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_k_170_);
lean_ctor_set(v_reuseFailAlloc_239_, 2, v_v_171_);
lean_ctor_set(v_reuseFailAlloc_239_, 3, v_l_172_);
lean_ctor_set(v_reuseFailAlloc_239_, 4, v___x_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_253_; 
v_l_253_ = lean_ctor_get(v_impl_166_, 3);
lean_inc(v_l_253_);
if (lean_obj_tag(v_l_253_) == 0)
{
lean_object* v_r_254_; lean_object* v_k_255_; lean_object* v_v_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_267_; 
v_r_254_ = lean_ctor_get(v_impl_166_, 4);
v_k_255_ = lean_ctor_get(v_impl_166_, 1);
v_v_256_ = lean_ctor_get(v_impl_166_, 2);
v_isSharedCheck_267_ = !lean_is_exclusive(v_impl_166_);
if (v_isSharedCheck_267_ == 0)
{
lean_object* v_unused_268_; lean_object* v_unused_269_; 
v_unused_268_ = lean_ctor_get(v_impl_166_, 3);
lean_dec(v_unused_268_);
v_unused_269_ = lean_ctor_get(v_impl_166_, 0);
lean_dec(v_unused_269_);
v___x_258_ = v_impl_166_;
v_isShared_259_ = v_isSharedCheck_267_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_r_254_);
lean_inc(v_v_256_);
lean_inc(v_k_255_);
lean_dec(v_impl_166_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_267_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_260_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_254_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 3, v_r_254_);
lean_ctor_set(v___x_258_, 2, v_v_20_);
lean_ctor_set(v___x_258_, 1, v_k_19_);
lean_ctor_set(v___x_258_, 0, v___x_167_);
v___x_262_ = v___x_258_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_k_19_);
lean_ctor_set(v_reuseFailAlloc_266_, 2, v_v_20_);
lean_ctor_set(v_reuseFailAlloc_266_, 3, v_r_254_);
lean_ctor_set(v_reuseFailAlloc_266_, 4, v_r_254_);
v___x_262_ = v_reuseFailAlloc_266_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_264_; 
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 4, v___x_262_);
lean_ctor_set(v___x_24_, 3, v_l_253_);
lean_ctor_set(v___x_24_, 2, v_v_256_);
lean_ctor_set(v___x_24_, 1, v_k_255_);
lean_ctor_set(v___x_24_, 0, v___x_260_);
v___x_264_ = v___x_24_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_260_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_k_255_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v_v_256_);
lean_ctor_set(v_reuseFailAlloc_265_, 3, v_l_253_);
lean_ctor_set(v_reuseFailAlloc_265_, 4, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
else
{
lean_object* v_r_270_; 
v_r_270_ = lean_ctor_get(v_impl_166_, 4);
lean_inc(v_r_270_);
if (lean_obj_tag(v_r_270_) == 0)
{
lean_object* v_k_271_; lean_object* v_v_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_295_; 
v_k_271_ = lean_ctor_get(v_impl_166_, 1);
v_v_272_ = lean_ctor_get(v_impl_166_, 2);
v_isSharedCheck_295_ = !lean_is_exclusive(v_impl_166_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; lean_object* v_unused_297_; lean_object* v_unused_298_; 
v_unused_296_ = lean_ctor_get(v_impl_166_, 4);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v_impl_166_, 3);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_impl_166_, 0);
lean_dec(v_unused_298_);
v___x_274_ = v_impl_166_;
v_isShared_275_ = v_isSharedCheck_295_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_v_272_);
lean_inc(v_k_271_);
lean_dec(v_impl_166_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_295_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v_k_276_; lean_object* v_v_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_291_; 
v_k_276_ = lean_ctor_get(v_r_270_, 1);
v_v_277_ = lean_ctor_get(v_r_270_, 2);
v_isSharedCheck_291_ = !lean_is_exclusive(v_r_270_);
if (v_isSharedCheck_291_ == 0)
{
lean_object* v_unused_292_; lean_object* v_unused_293_; lean_object* v_unused_294_; 
v_unused_292_ = lean_ctor_get(v_r_270_, 4);
lean_dec(v_unused_292_);
v_unused_293_ = lean_ctor_get(v_r_270_, 3);
lean_dec(v_unused_293_);
v_unused_294_ = lean_ctor_get(v_r_270_, 0);
lean_dec(v_unused_294_);
v___x_279_ = v_r_270_;
v_isShared_280_ = v_isSharedCheck_291_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_v_277_);
lean_inc(v_k_276_);
lean_dec(v_r_270_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_291_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_281_ = lean_unsigned_to_nat(3u);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 4, v_l_253_);
lean_ctor_set(v___x_279_, 3, v_l_253_);
lean_ctor_set(v___x_279_, 2, v_v_272_);
lean_ctor_set(v___x_279_, 1, v_k_271_);
lean_ctor_set(v___x_279_, 0, v___x_167_);
v___x_283_ = v___x_279_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_k_271_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v_v_272_);
lean_ctor_set(v_reuseFailAlloc_290_, 3, v_l_253_);
lean_ctor_set(v_reuseFailAlloc_290_, 4, v_l_253_);
v___x_283_ = v_reuseFailAlloc_290_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_285_; 
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 4, v_l_253_);
lean_ctor_set(v___x_274_, 2, v_v_20_);
lean_ctor_set(v___x_274_, 1, v_k_19_);
lean_ctor_set(v___x_274_, 0, v___x_167_);
v___x_285_ = v___x_274_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_k_19_);
lean_ctor_set(v_reuseFailAlloc_289_, 2, v_v_20_);
lean_ctor_set(v_reuseFailAlloc_289_, 3, v_l_253_);
lean_ctor_set(v_reuseFailAlloc_289_, 4, v_l_253_);
v___x_285_ = v_reuseFailAlloc_289_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_287_; 
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 4, v___x_285_);
lean_ctor_set(v___x_24_, 3, v___x_283_);
lean_ctor_set(v___x_24_, 2, v_v_277_);
lean_ctor_set(v___x_24_, 1, v_k_276_);
lean_ctor_set(v___x_24_, 0, v___x_281_);
v___x_287_ = v___x_24_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_k_276_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v_v_277_);
lean_ctor_set(v_reuseFailAlloc_288_, 3, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_288_, 4, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
}
}
else
{
lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_299_ = lean_unsigned_to_nat(2u);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 4, v_r_270_);
lean_ctor_set(v___x_24_, 3, v_impl_166_);
lean_ctor_set(v___x_24_, 0, v___x_299_);
v___x_301_ = v___x_24_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_k_19_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v_v_20_);
lean_ctor_set(v_reuseFailAlloc_302_, 3, v_impl_166_);
lean_ctor_set(v_reuseFailAlloc_302_, 4, v_r_270_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_unsigned_to_nat(1u);
v___x_305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v_k_15_);
lean_ctor_set(v___x_305_, 2, v_v_16_);
lean_ctor_set(v___x_305_, 3, v_t_17_);
lean_ctor_set(v___x_305_, 4, v_t_17_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkId(lean_object* v_id_306_, lean_object* v_a_307_){
_start:
{
uint8_t v___x_308_; 
v___x_308_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___redArg(v_id_306_, v_a_307_);
if (v___x_308_ == 0)
{
uint8_t v___x_309_; 
v___x_309_ = 1;
if (v___x_308_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_310_ = lean_box(0);
v___x_311_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_id_306_, v___x_310_, v_a_307_);
v___x_312_ = lean_box(v___x_309_);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_311_);
return v___x_313_;
}
else
{
lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v_id_306_);
v___x_314_ = lean_box(v___x_309_);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v_a_307_);
return v___x_315_;
}
}
else
{
uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec(v_id_306_);
v___x_316_ = 0;
v___x_317_ = lean_box(v___x_316_);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v_a_307_);
return v___x_318_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0(lean_object* v_00_u03b2_319_, lean_object* v_k_320_, lean_object* v_t_321_){
_start:
{
uint8_t v___x_322_; 
v___x_322_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___redArg(v_k_320_, v_t_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___boxed(lean_object* v_00_u03b2_323_, lean_object* v_k_324_, lean_object* v_t_325_){
_start:
{
uint8_t v_res_326_; lean_object* v_r_327_; 
v_res_326_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0(v_00_u03b2_323_, v_k_324_, v_t_325_);
lean_dec(v_t_325_);
lean_dec(v_k_324_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1(lean_object* v_00_u03b2_328_, lean_object* v_k_329_, lean_object* v_v_330_, lean_object* v_t_331_, lean_object* v_hl_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_k_329_, v_v_330_, v_t_331_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0(lean_object* v_as_334_, size_t v_i_335_, size_t v_stop_336_, lean_object* v___y_337_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = lean_usize_dec_eq(v_i_335_, v_stop_336_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v_x_340_; lean_object* v___x_341_; lean_object* v_fst_342_; lean_object* v_snd_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_360_; 
v___x_339_ = lean_array_uget_borrowed(v_as_334_, v_i_335_);
v_x_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_x_340_);
v___x_341_ = l_Lean_IR_UniqueIds_checkId(v_x_340_, v___y_337_);
v_fst_342_ = lean_ctor_get(v___x_341_, 0);
v_snd_343_ = lean_ctor_get(v___x_341_, 1);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_360_ == 0)
{
v___x_345_ = v___x_341_;
v_isShared_346_ = v_isSharedCheck_360_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_snd_343_);
lean_inc(v_fst_342_);
lean_dec(v___x_341_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_360_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
uint8_t v___x_347_; uint8_t v___x_348_; 
v___x_347_ = 1;
v___x_348_ = lean_unbox(v_fst_342_);
lean_dec(v_fst_342_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_351_; 
v___x_349_ = lean_box(v___x_347_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_349_);
v___x_351_ = v___x_345_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_snd_343_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
else
{
if (v___x_338_ == 0)
{
size_t v___x_353_; size_t v___x_354_; 
lean_del_object(v___x_345_);
v___x_353_ = ((size_t)1ULL);
v___x_354_ = lean_usize_add(v_i_335_, v___x_353_);
v_i_335_ = v___x_354_;
v___y_337_ = v_snd_343_;
goto _start;
}
else
{
lean_object* v___x_356_; lean_object* v___x_358_; 
v___x_356_ = lean_box(v___x_347_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_356_);
v___x_358_ = v___x_345_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_356_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_snd_343_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
}
else
{
uint8_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = 0;
v___x_362_ = lean_box(v___x_361_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v___y_337_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0___boxed(lean_object* v_as_364_, lean_object* v_i_365_, lean_object* v_stop_366_, lean_object* v___y_367_){
_start:
{
size_t v_i_boxed_368_; size_t v_stop_boxed_369_; lean_object* v_res_370_; 
v_i_boxed_368_ = lean_unbox_usize(v_i_365_);
lean_dec(v_i_365_);
v_stop_boxed_369_ = lean_unbox_usize(v_stop_366_);
lean_dec(v_stop_366_);
v_res_370_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0(v_as_364_, v_i_boxed_368_, v_stop_boxed_369_, v___y_367_);
lean_dec_ref(v_as_364_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkParams(lean_object* v_ps_371_, lean_object* v_a_372_){
_start:
{
lean_object* v___y_374_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = lean_array_get_size(v_ps_371_);
v___x_380_ = lean_nat_dec_lt(v___x_378_, v___x_379_);
if (v___x_380_ == 0)
{
v___y_374_ = v_a_372_;
goto v___jp_373_;
}
else
{
if (v___x_380_ == 0)
{
v___y_374_ = v_a_372_;
goto v___jp_373_;
}
else
{
size_t v___x_381_; size_t v___x_382_; lean_object* v___x_383_; lean_object* v_fst_384_; uint8_t v___x_385_; 
v___x_381_ = ((size_t)0ULL);
v___x_382_ = lean_usize_of_nat(v___x_379_);
v___x_383_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0(v_ps_371_, v___x_381_, v___x_382_, v_a_372_);
v_fst_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_fst_384_);
v___x_385_ = lean_unbox(v_fst_384_);
lean_dec(v_fst_384_);
if (v___x_385_ == 0)
{
lean_object* v_snd_386_; 
v_snd_386_ = lean_ctor_get(v___x_383_, 1);
lean_inc(v_snd_386_);
lean_dec_ref(v___x_383_);
v___y_374_ = v_snd_386_;
goto v___jp_373_;
}
else
{
lean_object* v_snd_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_396_; 
v_snd_387_ = lean_ctor_get(v___x_383_, 1);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; 
v_unused_397_ = lean_ctor_get(v___x_383_, 0);
lean_dec(v_unused_397_);
v___x_389_ = v___x_383_;
v_isShared_390_ = v_isSharedCheck_396_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_snd_387_);
lean_dec(v___x_383_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_396_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
uint8_t v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_391_ = 0;
v___x_392_ = lean_box(v___x_391_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_392_);
v___x_394_ = v___x_389_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_snd_387_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
v___jp_373_:
{
uint8_t v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = 1;
v___x_376_ = lean_box(v___x_375_);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v___y_374_);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkParams___boxed(lean_object* v_ps_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_IR_UniqueIds_checkParams(v_ps_398_, v_a_399_);
lean_dec_ref(v_ps_398_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkFnBody(lean_object* v_x_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___y_404_; 
switch(lean_obj_tag(v_x_401_))
{
case 0:
{
lean_object* v_x_408_; lean_object* v_b_409_; lean_object* v___x_410_; lean_object* v_fst_411_; uint8_t v___x_412_; 
v_x_408_ = lean_ctor_get(v_x_401_, 0);
lean_inc(v_x_408_);
v_b_409_ = lean_ctor_get(v_x_401_, 3);
lean_inc(v_b_409_);
lean_dec_ref(v_x_401_);
v___x_410_ = l_Lean_IR_UniqueIds_checkId(v_x_408_, v_a_402_);
v_fst_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_fst_411_);
v___x_412_ = lean_unbox(v_fst_411_);
lean_dec(v_fst_411_);
if (v___x_412_ == 0)
{
lean_dec(v_b_409_);
return v___x_410_;
}
else
{
lean_object* v_snd_413_; 
v_snd_413_ = lean_ctor_get(v___x_410_, 1);
lean_inc(v_snd_413_);
lean_dec_ref(v___x_410_);
v_x_401_ = v_b_409_;
v_a_402_ = v_snd_413_;
goto _start;
}
}
case 1:
{
lean_object* v_j_415_; lean_object* v_xs_416_; lean_object* v_b_417_; lean_object* v___x_418_; lean_object* v_fst_419_; uint8_t v___x_420_; 
v_j_415_ = lean_ctor_get(v_x_401_, 0);
lean_inc(v_j_415_);
v_xs_416_ = lean_ctor_get(v_x_401_, 1);
lean_inc_ref(v_xs_416_);
v_b_417_ = lean_ctor_get(v_x_401_, 3);
lean_inc(v_b_417_);
lean_dec_ref(v_x_401_);
v___x_418_ = l_Lean_IR_UniqueIds_checkId(v_j_415_, v_a_402_);
v_fst_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_fst_419_);
v___x_420_ = lean_unbox(v_fst_419_);
lean_dec(v_fst_419_);
if (v___x_420_ == 0)
{
lean_dec(v_b_417_);
lean_dec_ref(v_xs_416_);
return v___x_418_;
}
else
{
lean_object* v_snd_421_; lean_object* v___x_422_; lean_object* v_fst_423_; uint8_t v___x_424_; 
v_snd_421_ = lean_ctor_get(v___x_418_, 1);
lean_inc(v_snd_421_);
lean_dec_ref(v___x_418_);
v___x_422_ = l_Lean_IR_UniqueIds_checkParams(v_xs_416_, v_snd_421_);
lean_dec_ref(v_xs_416_);
v_fst_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_fst_423_);
v___x_424_ = lean_unbox(v_fst_423_);
lean_dec(v_fst_423_);
if (v___x_424_ == 0)
{
lean_dec(v_b_417_);
return v___x_422_;
}
else
{
lean_object* v_snd_425_; 
v_snd_425_ = lean_ctor_get(v___x_422_, 1);
lean_inc(v_snd_425_);
lean_dec_ref(v___x_422_);
v_x_401_ = v_b_417_;
v_a_402_ = v_snd_425_;
goto _start;
}
}
}
case 9:
{
lean_object* v_cs_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v_cs_427_ = lean_ctor_get(v_x_401_, 3);
lean_inc_ref(v_cs_427_);
lean_dec_ref(v_x_401_);
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = lean_array_get_size(v_cs_427_);
v___x_430_ = lean_nat_dec_lt(v___x_428_, v___x_429_);
if (v___x_430_ == 0)
{
lean_dec_ref(v_cs_427_);
v___y_404_ = v_a_402_;
goto v___jp_403_;
}
else
{
if (v___x_430_ == 0)
{
lean_dec_ref(v_cs_427_);
v___y_404_ = v_a_402_;
goto v___jp_403_;
}
else
{
size_t v___x_431_; size_t v___x_432_; lean_object* v___x_433_; lean_object* v_fst_434_; uint8_t v___x_435_; 
v___x_431_ = ((size_t)0ULL);
v___x_432_ = lean_usize_of_nat(v___x_429_);
v___x_433_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(v_cs_427_, v___x_431_, v___x_432_, v_a_402_);
lean_dec_ref(v_cs_427_);
v_fst_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_fst_434_);
v___x_435_ = lean_unbox(v_fst_434_);
lean_dec(v_fst_434_);
if (v___x_435_ == 0)
{
lean_object* v_snd_436_; 
v_snd_436_ = lean_ctor_get(v___x_433_, 1);
lean_inc(v_snd_436_);
lean_dec_ref(v___x_433_);
v___y_404_ = v_snd_436_;
goto v___jp_403_;
}
else
{
lean_object* v_snd_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_446_; 
v_snd_437_ = lean_ctor_get(v___x_433_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; 
v_unused_447_ = lean_ctor_get(v___x_433_, 0);
lean_dec(v_unused_447_);
v___x_439_ = v___x_433_;
v_isShared_440_ = v_isSharedCheck_446_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_snd_437_);
lean_dec(v___x_433_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_446_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
uint8_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_441_ = 0;
v___x_442_ = lean_box(v___x_441_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_442_);
v___x_444_ = v___x_439_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_snd_437_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
}
default: 
{
uint8_t v___x_448_; 
v___x_448_ = l_Lean_IR_FnBody_isTerminal(v_x_401_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_IR_FnBody_body(v_x_401_);
lean_dec(v_x_401_);
v_x_401_ = v___x_449_;
goto _start;
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; 
lean_dec(v_x_401_);
v___x_451_ = lean_box(v___x_448_);
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
lean_ctor_set(v___x_452_, 1, v_a_402_);
return v___x_452_;
}
}
}
v___jp_403_:
{
uint8_t v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = 1;
v___x_406_ = lean_box(v___x_405_);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___y_404_);
return v___x_407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(lean_object* v_as_453_, size_t v_i_454_, size_t v_stop_455_, lean_object* v___y_456_){
_start:
{
uint8_t v___x_457_; 
v___x_457_ = lean_usize_dec_eq(v_i_454_, v_stop_455_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v_fst_461_; lean_object* v_snd_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_479_; 
v___x_458_ = lean_array_uget_borrowed(v_as_453_, v_i_454_);
v___x_459_ = l_Lean_IR_Alt_body(v___x_458_);
v___x_460_ = l_Lean_IR_UniqueIds_checkFnBody(v___x_459_, v___y_456_);
v_fst_461_ = lean_ctor_get(v___x_460_, 0);
v_snd_462_ = lean_ctor_get(v___x_460_, 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_479_ == 0)
{
v___x_464_ = v___x_460_;
v_isShared_465_ = v_isSharedCheck_479_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_snd_462_);
lean_inc(v_fst_461_);
lean_dec(v___x_460_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_479_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
uint8_t v___x_466_; uint8_t v___x_467_; 
v___x_466_ = 1;
v___x_467_ = lean_unbox(v_fst_461_);
lean_dec(v_fst_461_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_468_ = lean_box(v___x_466_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_468_);
v___x_470_ = v___x_464_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_snd_462_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
else
{
if (v___x_457_ == 0)
{
size_t v___x_472_; size_t v___x_473_; 
lean_del_object(v___x_464_);
v___x_472_ = ((size_t)1ULL);
v___x_473_ = lean_usize_add(v_i_454_, v___x_472_);
v_i_454_ = v___x_473_;
v___y_456_ = v_snd_462_;
goto _start;
}
else
{
lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_475_ = lean_box(v___x_466_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_475_);
v___x_477_ = v___x_464_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_snd_462_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
else
{
uint8_t v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = 0;
v___x_481_ = lean_box(v___x_480_);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v___y_456_);
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0___boxed(lean_object* v_as_483_, lean_object* v_i_484_, lean_object* v_stop_485_, lean_object* v___y_486_){
_start:
{
size_t v_i_boxed_487_; size_t v_stop_boxed_488_; lean_object* v_res_489_; 
v_i_boxed_487_ = lean_unbox_usize(v_i_484_);
lean_dec(v_i_484_);
v_stop_boxed_488_ = lean_unbox_usize(v_stop_485_);
lean_dec(v_stop_485_);
v_res_489_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(v_as_483_, v_i_boxed_487_, v_stop_boxed_488_, v___y_486_);
lean_dec_ref(v_as_483_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkDecl(lean_object* v_x_490_, lean_object* v_a_491_){
_start:
{
if (lean_obj_tag(v_x_490_) == 0)
{
lean_object* v_xs_492_; lean_object* v_body_493_; lean_object* v___x_494_; lean_object* v_fst_495_; uint8_t v___x_496_; 
v_xs_492_ = lean_ctor_get(v_x_490_, 1);
lean_inc_ref(v_xs_492_);
v_body_493_ = lean_ctor_get(v_x_490_, 3);
lean_inc(v_body_493_);
lean_dec_ref(v_x_490_);
v___x_494_ = l_Lean_IR_UniqueIds_checkParams(v_xs_492_, v_a_491_);
lean_dec_ref(v_xs_492_);
v_fst_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_fst_495_);
v___x_496_ = lean_unbox(v_fst_495_);
lean_dec(v_fst_495_);
if (v___x_496_ == 0)
{
lean_dec(v_body_493_);
return v___x_494_;
}
else
{
lean_object* v_snd_497_; lean_object* v___x_498_; 
v_snd_497_ = lean_ctor_get(v___x_494_, 1);
lean_inc(v_snd_497_);
lean_dec_ref(v___x_494_);
v___x_498_ = l_Lean_IR_UniqueIds_checkFnBody(v_body_493_, v_snd_497_);
return v___x_498_;
}
}
else
{
lean_object* v_xs_499_; lean_object* v___x_500_; 
v_xs_499_ = lean_ctor_get(v_x_490_, 1);
lean_inc_ref(v_xs_499_);
lean_dec_ref(v_x_490_);
v___x_500_ = l_Lean_IR_UniqueIds_checkParams(v_xs_499_, v_a_491_);
lean_dec_ref(v_xs_499_);
return v___x_500_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Decl_uniqueIds(lean_object* v_d_501_){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v_fst_504_; uint8_t v___x_505_; 
v___x_502_ = lean_box(1);
v___x_503_ = l_Lean_IR_UniqueIds_checkDecl(v_d_501_, v___x_502_);
v_fst_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_fst_504_);
lean_dec_ref(v___x_503_);
v___x_505_ = lean_unbox(v_fst_504_);
lean_dec(v_fst_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_uniqueIds___boxed(lean_object* v_d_506_){
_start:
{
uint8_t v_res_507_; lean_object* v_r_508_; 
v_res_507_ = l_Lean_IR_Decl_uniqueIds(v_d_506_);
v_r_508_ = lean_box(v_res_507_);
return v_r_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(lean_object* v_t_509_, lean_object* v_k_510_){
_start:
{
if (lean_obj_tag(v_t_509_) == 0)
{
lean_object* v_k_511_; lean_object* v_v_512_; lean_object* v_l_513_; lean_object* v_r_514_; uint8_t v___x_515_; 
v_k_511_ = lean_ctor_get(v_t_509_, 1);
v_v_512_ = lean_ctor_get(v_t_509_, 2);
v_l_513_ = lean_ctor_get(v_t_509_, 3);
v_r_514_ = lean_ctor_get(v_t_509_, 4);
v___x_515_ = lean_nat_dec_lt(v_k_510_, v_k_511_);
if (v___x_515_ == 0)
{
uint8_t v___x_516_; 
v___x_516_ = lean_nat_dec_eq(v_k_510_, v_k_511_);
if (v___x_516_ == 0)
{
v_t_509_ = v_r_514_;
goto _start;
}
else
{
lean_object* v___x_518_; 
lean_inc(v_v_512_);
v___x_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_518_, 0, v_v_512_);
return v___x_518_;
}
}
else
{
v_t_509_ = v_l_513_;
goto _start;
}
}
else
{
lean_object* v___x_520_; 
v___x_520_ = lean_box(0);
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg___boxed(lean_object* v_t_521_, lean_object* v_k_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_t_521_, v_k_522_);
lean_dec(v_k_522_);
lean_dec(v_t_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normIndex(lean_object* v_x_524_, lean_object* v_m_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_m_525_, v_x_524_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_inc(v_x_524_);
return v_x_524_;
}
else
{
lean_object* v_val_527_; 
v_val_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_val_527_);
lean_dec_ref(v___x_526_);
return v_val_527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normIndex___boxed(lean_object* v_x_528_, lean_object* v_m_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_IR_NormalizeIds_normIndex(v_x_528_, v_m_529_);
lean_dec(v_m_529_);
lean_dec(v_x_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0(lean_object* v_00_u03b4_531_, lean_object* v_t_532_, lean_object* v_k_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_t_532_, v_k_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___boxed(lean_object* v_00_u03b4_535_, lean_object* v_t_536_, lean_object* v_k_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0(v_00_u03b4_535_, v_t_536_, v_k_537_);
lean_dec(v_k_537_);
lean_dec(v_t_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normVar(lean_object* v_x_539_, lean_object* v_a_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_IR_NormalizeIds_normIndex(v_x_539_, v_a_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normVar___boxed(lean_object* v_x_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_IR_NormalizeIds_normVar(v_x_542_, v_a_543_);
lean_dec(v_a_543_);
lean_dec(v_x_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normJP(lean_object* v_x_545_, lean_object* v_a_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_IR_NormalizeIds_normIndex(v_x_545_, v_a_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normJP___boxed(lean_object* v_x_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_IR_NormalizeIds_normJP(v_x_548_, v_a_549_);
lean_dec(v_a_549_);
lean_dec(v_x_548_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArg(lean_object* v_x_551_, lean_object* v_a_552_){
_start:
{
if (lean_obj_tag(v_x_551_) == 0)
{
lean_object* v_id_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_561_; 
v_id_553_ = lean_ctor_get(v_x_551_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v_x_551_);
if (v_isSharedCheck_561_ == 0)
{
v___x_555_ = v_x_551_;
v_isShared_556_ = v_isSharedCheck_561_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_id_553_);
lean_dec(v_x_551_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_561_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_557_ = l_Lean_IR_NormalizeIds_normIndex(v_id_553_, v_a_552_);
lean_dec(v_id_553_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_557_);
v___x_559_ = v___x_555_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
else
{
return v_x_551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArg___boxed(lean_object* v_x_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_IR_NormalizeIds_normArg(v_x_562_, v_a_563_);
lean_dec(v_a_563_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(lean_object* v_m_565_, size_t v_sz_566_, size_t v_i_567_, lean_object* v_bs_568_){
_start:
{
uint8_t v___x_569_; 
v___x_569_ = lean_usize_dec_lt(v_i_567_, v_sz_566_);
if (v___x_569_ == 0)
{
return v_bs_568_;
}
else
{
lean_object* v_v_570_; lean_object* v___x_571_; lean_object* v_bs_x27_572_; lean_object* v___x_573_; size_t v___x_574_; size_t v___x_575_; lean_object* v___x_576_; 
v_v_570_ = lean_array_uget(v_bs_568_, v_i_567_);
v___x_571_ = lean_unsigned_to_nat(0u);
v_bs_x27_572_ = lean_array_uset(v_bs_568_, v_i_567_, v___x_571_);
v___x_573_ = l_Lean_IR_NormalizeIds_normArg(v_v_570_, v_m_565_);
v___x_574_ = ((size_t)1ULL);
v___x_575_ = lean_usize_add(v_i_567_, v___x_574_);
v___x_576_ = lean_array_uset(v_bs_x27_572_, v_i_567_, v___x_573_);
v_i_567_ = v___x_575_;
v_bs_568_ = v___x_576_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0___boxed(lean_object* v_m_578_, lean_object* v_sz_579_, lean_object* v_i_580_, lean_object* v_bs_581_){
_start:
{
size_t v_sz_boxed_582_; size_t v_i_boxed_583_; lean_object* v_res_584_; 
v_sz_boxed_582_ = lean_unbox_usize(v_sz_579_);
lean_dec(v_sz_579_);
v_i_boxed_583_ = lean_unbox_usize(v_i_580_);
lean_dec(v_i_580_);
v_res_584_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(v_m_578_, v_sz_boxed_582_, v_i_boxed_583_, v_bs_581_);
lean_dec(v_m_578_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArgs(lean_object* v_as_585_, lean_object* v_m_586_){
_start:
{
size_t v_sz_587_; size_t v___x_588_; lean_object* v___x_589_; 
v_sz_587_ = lean_array_size(v_as_585_);
v___x_588_ = ((size_t)0ULL);
v___x_589_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(v_m_586_, v_sz_587_, v___x_588_, v_as_585_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArgs___boxed(lean_object* v_as_590_, lean_object* v_m_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_IR_NormalizeIds_normArgs(v_as_590_, v_m_591_);
lean_dec(v_m_591_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normExpr(lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
switch(lean_obj_tag(v_x_593_))
{
case 0:
{
lean_object* v_i_595_; lean_object* v_ys_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_604_; 
v_i_595_ = lean_ctor_get(v_x_593_, 0);
v_ys_596_ = lean_ctor_get(v_x_593_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_604_ == 0)
{
v___x_598_ = v_x_593_;
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_ys_596_);
lean_inc(v_i_595_);
lean_dec(v_x_593_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_596_, v_x_594_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 1, v___x_600_);
v___x_602_ = v___x_598_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_i_595_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
case 1:
{
lean_object* v_n_605_; lean_object* v_x_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_614_; 
v_n_605_ = lean_ctor_get(v_x_593_, 0);
v_x_606_ = lean_ctor_get(v_x_593_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_614_ == 0)
{
v___x_608_ = v_x_593_;
v_isShared_609_ = v_isSharedCheck_614_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_x_606_);
lean_inc(v_n_605_);
lean_dec(v_x_593_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_614_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_610_ = l_Lean_IR_NormalizeIds_normIndex(v_x_606_, v_x_594_);
lean_dec(v_x_606_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v___x_610_);
v___x_612_ = v___x_608_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_n_605_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
case 2:
{
lean_object* v_x_615_; lean_object* v_i_616_; uint8_t v_updtHeader_617_; lean_object* v_ys_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_627_; 
v_x_615_ = lean_ctor_get(v_x_593_, 0);
v_i_616_ = lean_ctor_get(v_x_593_, 1);
v_updtHeader_617_ = lean_ctor_get_uint8(v_x_593_, sizeof(void*)*3);
v_ys_618_ = lean_ctor_get(v_x_593_, 2);
v_isSharedCheck_627_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_627_ == 0)
{
v___x_620_ = v_x_593_;
v_isShared_621_ = v_isSharedCheck_627_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_ys_618_);
lean_inc(v_i_616_);
lean_inc(v_x_615_);
lean_dec(v_x_593_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_627_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_622_ = l_Lean_IR_NormalizeIds_normIndex(v_x_615_, v_x_594_);
lean_dec(v_x_615_);
v___x_623_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_618_, v_x_594_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 2, v___x_623_);
lean_ctor_set(v___x_620_, 0, v___x_622_);
v___x_625_ = v___x_620_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_i_616_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v___x_623_);
lean_ctor_set_uint8(v_reuseFailAlloc_626_, sizeof(void*)*3, v_updtHeader_617_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
case 3:
{
lean_object* v_i_628_; lean_object* v_x_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_637_; 
v_i_628_ = lean_ctor_get(v_x_593_, 0);
v_x_629_ = lean_ctor_get(v_x_593_, 1);
v_isSharedCheck_637_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_637_ == 0)
{
v___x_631_ = v_x_593_;
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_x_629_);
lean_inc(v_i_628_);
lean_dec(v_x_593_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_633_ = l_Lean_IR_NormalizeIds_normIndex(v_x_629_, v_x_594_);
lean_dec(v_x_629_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 1, v___x_633_);
v___x_635_ = v___x_631_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_i_628_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
case 4:
{
lean_object* v_i_638_; lean_object* v_x_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_647_; 
v_i_638_ = lean_ctor_get(v_x_593_, 0);
v_x_639_ = lean_ctor_get(v_x_593_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_647_ == 0)
{
v___x_641_ = v_x_593_;
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_x_639_);
lean_inc(v_i_638_);
lean_dec(v_x_593_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_643_ = l_Lean_IR_NormalizeIds_normIndex(v_x_639_, v_x_594_);
lean_dec(v_x_639_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v___x_643_);
v___x_645_ = v___x_641_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_i_638_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
case 5:
{
lean_object* v_n_648_; lean_object* v_offset_649_; lean_object* v_x_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_658_; 
v_n_648_ = lean_ctor_get(v_x_593_, 0);
v_offset_649_ = lean_ctor_get(v_x_593_, 1);
v_x_650_ = lean_ctor_get(v_x_593_, 2);
v_isSharedCheck_658_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_658_ == 0)
{
v___x_652_ = v_x_593_;
v_isShared_653_ = v_isSharedCheck_658_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_x_650_);
lean_inc(v_offset_649_);
lean_inc(v_n_648_);
lean_dec(v_x_593_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_658_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_654_ = l_Lean_IR_NormalizeIds_normIndex(v_x_650_, v_x_594_);
lean_dec(v_x_650_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 2, v___x_654_);
v___x_656_ = v___x_652_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_n_648_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_offset_649_);
lean_ctor_set(v_reuseFailAlloc_657_, 2, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
case 6:
{
lean_object* v_c_659_; lean_object* v_ys_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_668_; 
v_c_659_ = lean_ctor_get(v_x_593_, 0);
v_ys_660_ = lean_ctor_get(v_x_593_, 1);
v_isSharedCheck_668_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_668_ == 0)
{
v___x_662_ = v_x_593_;
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_ys_660_);
lean_inc(v_c_659_);
lean_dec(v_x_593_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_664_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_660_, v_x_594_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 1, v___x_664_);
v___x_666_ = v___x_662_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_c_659_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
case 7:
{
lean_object* v_c_669_; lean_object* v_ys_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_678_; 
v_c_669_ = lean_ctor_get(v_x_593_, 0);
v_ys_670_ = lean_ctor_get(v_x_593_, 1);
v_isSharedCheck_678_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_678_ == 0)
{
v___x_672_ = v_x_593_;
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_ys_670_);
lean_inc(v_c_669_);
lean_dec(v_x_593_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_674_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_670_, v_x_594_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 1, v___x_674_);
v___x_676_ = v___x_672_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_c_669_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
case 8:
{
lean_object* v_x_679_; lean_object* v_ys_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_689_; 
v_x_679_ = lean_ctor_get(v_x_593_, 0);
v_ys_680_ = lean_ctor_get(v_x_593_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_689_ == 0)
{
v___x_682_ = v_x_593_;
v_isShared_683_ = v_isSharedCheck_689_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_ys_680_);
lean_inc(v_x_679_);
lean_dec(v_x_593_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_689_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_684_ = l_Lean_IR_NormalizeIds_normIndex(v_x_679_, v_x_594_);
lean_dec(v_x_679_);
v___x_685_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_680_, v_x_594_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v___x_685_);
lean_ctor_set(v___x_682_, 0, v___x_684_);
v___x_687_ = v___x_682_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
case 9:
{
lean_object* v_ty_690_; lean_object* v_x_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_699_; 
v_ty_690_ = lean_ctor_get(v_x_593_, 0);
v_x_691_ = lean_ctor_get(v_x_593_, 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_699_ == 0)
{
v___x_693_ = v_x_593_;
v_isShared_694_ = v_isSharedCheck_699_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_x_691_);
lean_inc(v_ty_690_);
lean_dec(v_x_593_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_699_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_695_ = l_Lean_IR_NormalizeIds_normIndex(v_x_691_, v_x_594_);
lean_dec(v_x_691_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v___x_695_);
v___x_697_ = v___x_693_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_ty_690_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
case 10:
{
lean_object* v_x_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_708_; 
v_x_700_ = lean_ctor_get(v_x_593_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_708_ == 0)
{
v___x_702_ = v_x_593_;
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_x_700_);
lean_dec(v_x_593_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_704_ = l_Lean_IR_NormalizeIds_normIndex(v_x_700_, v_x_594_);
lean_dec(v_x_700_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_704_);
v___x_706_ = v___x_702_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
case 11:
{
return v_x_593_;
}
default: 
{
lean_object* v_x_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_717_; 
v_x_709_ = lean_ctor_get(v_x_593_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_717_ == 0)
{
v___x_711_ = v_x_593_;
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_x_709_);
lean_dec(v_x_593_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_713_ = l_Lean_IR_NormalizeIds_normIndex(v_x_709_, v_x_594_);
lean_dec(v_x_709_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normExpr___boxed(lean_object* v_x_718_, lean_object* v_x_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_IR_NormalizeIds_normExpr(v_x_718_, v_x_719_);
lean_dec(v_x_719_);
return v_res_720_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_NormalizeIds_withVar___redArg___lam__0(lean_object* v_x_721_, lean_object* v_y_722_){
_start:
{
uint8_t v___x_723_; 
v___x_723_ = lean_nat_dec_lt(v_x_721_, v_y_722_);
if (v___x_723_ == 0)
{
uint8_t v___x_724_; 
v___x_724_ = lean_nat_dec_eq(v_x_721_, v_y_722_);
if (v___x_724_ == 0)
{
uint8_t v___x_725_; 
v___x_725_ = 2;
return v___x_725_;
}
else
{
uint8_t v___x_726_; 
v___x_726_ = 1;
return v___x_726_;
}
}
else
{
uint8_t v___x_727_; 
v___x_727_ = 0;
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg___lam__0___boxed(lean_object* v_x_728_, lean_object* v_y_729_){
_start:
{
uint8_t v_res_730_; lean_object* v_r_731_; 
v_res_730_ = l_Lean_IR_NormalizeIds_withVar___redArg___lam__0(v_x_728_, v_y_729_);
lean_dec(v_y_729_);
lean_dec(v_x_728_);
v_r_731_ = lean_box(v_res_730_);
return v_r_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg(lean_object* v_x_733_, lean_object* v_k_734_, lean_object* v_m_735_, lean_object* v_a_736_){
_start:
{
lean_object* v___f_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___f_737_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_738_ = lean_unsigned_to_nat(1u);
v___x_739_ = lean_nat_add(v_a_736_, v___x_738_);
lean_inc(v_a_736_);
v___x_740_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_737_, v_x_733_, v_a_736_, v_m_735_);
v___x_741_ = lean_apply_3(v_k_734_, v_a_736_, v___x_740_, v___x_739_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar(lean_object* v_00_u03b1_742_, lean_object* v_x_743_, lean_object* v_k_744_, lean_object* v_m_745_, lean_object* v_a_746_){
_start:
{
lean_object* v___f_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___f_747_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_748_ = lean_unsigned_to_nat(1u);
v___x_749_ = lean_nat_add(v_a_746_, v___x_748_);
lean_inc(v_a_746_);
v___x_750_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_747_, v_x_743_, v_a_746_, v_m_745_);
v___x_751_ = lean_apply_3(v_k_744_, v_a_746_, v___x_750_, v___x_749_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___redArg(lean_object* v_x_752_, lean_object* v_k_753_, lean_object* v_m_754_, lean_object* v_a_755_){
_start:
{
lean_object* v___f_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___f_756_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_757_ = lean_unsigned_to_nat(1u);
v___x_758_ = lean_nat_add(v_a_755_, v___x_757_);
lean_inc(v_a_755_);
v___x_759_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_756_, v_x_752_, v_a_755_, v_m_754_);
v___x_760_ = lean_apply_3(v_k_753_, v_a_755_, v___x_759_, v___x_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP(lean_object* v_00_u03b1_761_, lean_object* v_x_762_, lean_object* v_k_763_, lean_object* v_m_764_, lean_object* v_a_765_){
_start:
{
lean_object* v___f_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___f_766_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_767_ = lean_unsigned_to_nat(1u);
v___x_768_ = lean_nat_add(v_a_765_, v___x_767_);
lean_inc(v_a_765_);
v___x_769_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_766_, v_x_762_, v_a_765_, v_m_764_);
v___x_770_ = lean_apply_3(v_k_763_, v_a_765_, v___x_769_, v___x_768_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__0(lean_object* v_fst_771_, lean_object* v_x_772_){
_start:
{
lean_object* v_x_773_; uint8_t v_borrow_774_; lean_object* v_ty_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_783_; 
v_x_773_ = lean_ctor_get(v_x_772_, 0);
v_borrow_774_ = lean_ctor_get_uint8(v_x_772_, sizeof(void*)*2);
v_ty_775_ = lean_ctor_get(v_x_772_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v_x_772_);
if (v_isSharedCheck_783_ == 0)
{
v___x_777_ = v_x_772_;
v_isShared_778_ = v_isSharedCheck_783_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_ty_775_);
lean_inc(v_x_773_);
lean_dec(v_x_772_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_783_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_779_ = l_Lean_IR_NormalizeIds_normIndex(v_x_773_, v_fst_771_);
lean_dec(v_x_773_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_779_);
v___x_781_ = v___x_777_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_ty_775_);
lean_ctor_set_uint8(v_reuseFailAlloc_782_, sizeof(void*)*2, v_borrow_774_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed(lean_object* v_fst_784_, lean_object* v_x_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_IR_NormalizeIds_withParams___redArg___lam__0(v_fst_784_, v_x_785_);
lean_dec(v_fst_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__2(lean_object* v___f_787_, lean_object* v_m_788_, lean_object* v_p_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_x_791_ = lean_ctor_get(v_p_789_, 0);
lean_inc(v_x_791_);
lean_dec_ref(v_p_789_);
v___x_792_ = lean_unsigned_to_nat(1u);
v___x_793_ = lean_nat_add(v___y_790_, v___x_792_);
v___x_794_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_787_, v_x_791_, v___y_790_, v_m_788_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
lean_ctor_set(v___x_795_, 1, v___x_793_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg(lean_object* v_ps_843_, lean_object* v_k_844_, lean_object* v_m_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___x_847_; lean_object* v_fst_849_; lean_object* v_snd_850_; lean_object* v___y_857_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_847_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__9));
v___x_860_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__19));
v___x_861_ = lean_unsigned_to_nat(0u);
v___x_862_ = lean_array_get_size(v_ps_843_);
v___x_863_ = lean_nat_dec_lt(v___x_861_, v___x_862_);
if (v___x_863_ == 0)
{
v_fst_849_ = v_m_845_;
v_snd_850_ = v_a_846_;
goto v___jp_848_;
}
else
{
lean_object* v___f_864_; uint8_t v___x_865_; 
v___f_864_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__20));
v___x_865_ = lean_nat_dec_le(v___x_862_, v___x_862_);
if (v___x_865_ == 0)
{
if (v___x_863_ == 0)
{
v_fst_849_ = v_m_845_;
v_snd_850_ = v_a_846_;
goto v___jp_848_;
}
else
{
size_t v___x_866_; size_t v___x_867_; lean_object* v___x_793__overap_868_; lean_object* v___x_869_; 
v___x_866_ = ((size_t)0ULL);
v___x_867_ = lean_usize_of_nat(v___x_862_);
lean_inc_ref(v_ps_843_);
v___x_793__overap_868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_860_, v___f_864_, v_ps_843_, v___x_866_, v___x_867_, v_m_845_);
v___x_869_ = lean_apply_1(v___x_793__overap_868_, v_a_846_);
v___y_857_ = v___x_869_;
goto v___jp_856_;
}
}
else
{
size_t v___x_870_; size_t v___x_871_; lean_object* v___x_798__overap_872_; lean_object* v___x_873_; 
v___x_870_ = ((size_t)0ULL);
v___x_871_ = lean_usize_of_nat(v___x_862_);
lean_inc_ref(v_ps_843_);
v___x_798__overap_872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_860_, v___f_864_, v_ps_843_, v___x_870_, v___x_871_, v_m_845_);
v___x_873_ = lean_apply_1(v___x_798__overap_872_, v_a_846_);
v___y_857_ = v___x_873_;
goto v___jp_856_;
}
}
v___jp_848_:
{
lean_object* v___f_851_; size_t v_sz_852_; size_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
lean_inc(v_fst_849_);
v___f_851_ = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_851_, 0, v_fst_849_);
v_sz_852_ = lean_array_size(v_ps_843_);
v___x_853_ = ((size_t)0ULL);
v___x_854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_847_, v___f_851_, v_sz_852_, v___x_853_, v_ps_843_);
v___x_855_ = lean_apply_3(v_k_844_, v___x_854_, v_fst_849_, v_snd_850_);
return v___x_855_;
}
v___jp_856_:
{
lean_object* v_fst_858_; lean_object* v_snd_859_; 
v_fst_858_ = lean_ctor_get(v___y_857_, 0);
lean_inc(v_fst_858_);
v_snd_859_ = lean_ctor_get(v___y_857_, 1);
lean_inc(v_snd_859_);
lean_dec_ref(v___y_857_);
v_fst_849_ = v_fst_858_;
v_snd_850_ = v_snd_859_;
goto v___jp_848_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams(lean_object* v_00_u03b1_874_, lean_object* v_ps_875_, lean_object* v_k_876_, lean_object* v_m_877_, lean_object* v_a_878_){
_start:
{
lean_object* v___x_879_; lean_object* v_fst_881_; lean_object* v_snd_882_; lean_object* v___y_889_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_879_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__9));
v___x_892_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__19));
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = lean_array_get_size(v_ps_875_);
v___x_895_ = lean_nat_dec_lt(v___x_893_, v___x_894_);
if (v___x_895_ == 0)
{
v_fst_881_ = v_m_877_;
v_snd_882_ = v_a_878_;
goto v___jp_880_;
}
else
{
lean_object* v___f_896_; uint8_t v___x_897_; 
v___f_896_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__20));
v___x_897_ = lean_nat_dec_le(v___x_894_, v___x_894_);
if (v___x_897_ == 0)
{
if (v___x_895_ == 0)
{
v_fst_881_ = v_m_877_;
v_snd_882_ = v_a_878_;
goto v___jp_880_;
}
else
{
size_t v___x_898_; size_t v___x_899_; lean_object* v___x_975__overap_900_; lean_object* v___x_901_; 
v___x_898_ = ((size_t)0ULL);
v___x_899_ = lean_usize_of_nat(v___x_894_);
lean_inc_ref(v_ps_875_);
v___x_975__overap_900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_892_, v___f_896_, v_ps_875_, v___x_898_, v___x_899_, v_m_877_);
v___x_901_ = lean_apply_1(v___x_975__overap_900_, v_a_878_);
v___y_889_ = v___x_901_;
goto v___jp_888_;
}
}
else
{
size_t v___x_902_; size_t v___x_903_; lean_object* v___x_978__overap_904_; lean_object* v___x_905_; 
v___x_902_ = ((size_t)0ULL);
v___x_903_ = lean_usize_of_nat(v___x_894_);
lean_inc_ref(v_ps_875_);
v___x_978__overap_904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_892_, v___f_896_, v_ps_875_, v___x_902_, v___x_903_, v_m_877_);
v___x_905_ = lean_apply_1(v___x_978__overap_904_, v_a_878_);
v___y_889_ = v___x_905_;
goto v___jp_888_;
}
}
v___jp_880_:
{
lean_object* v___f_883_; size_t v_sz_884_; size_t v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
lean_inc(v_fst_881_);
v___f_883_ = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_883_, 0, v_fst_881_);
v_sz_884_ = lean_array_size(v_ps_875_);
v___x_885_ = ((size_t)0ULL);
v___x_886_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_879_, v___f_883_, v_sz_884_, v___x_885_, v_ps_875_);
v___x_887_ = lean_apply_3(v_k_876_, v___x_886_, v_fst_881_, v_snd_882_);
return v___x_887_;
}
v___jp_888_:
{
lean_object* v_fst_890_; lean_object* v_snd_891_; 
v_fst_890_ = lean_ctor_get(v___y_889_, 0);
lean_inc(v_fst_890_);
v_snd_891_ = lean_ctor_get(v___y_889_, 1);
lean_inc(v_snd_891_);
lean_dec_ref(v___y_889_);
v_fst_881_ = v_fst_890_;
v_snd_882_ = v_snd_891_;
goto v___jp_880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_instMonadLiftMN___lam__0(lean_object* v_00_u03b1_906_, lean_object* v_x_907_, lean_object* v_m_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = lean_apply_1(v_x_907_, v_m_908_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v___y_909_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(lean_object* v_fst_914_, size_t v_sz_915_, size_t v_i_916_, lean_object* v_bs_917_){
_start:
{
uint8_t v___x_918_; 
v___x_918_ = lean_usize_dec_lt(v_i_916_, v_sz_915_);
if (v___x_918_ == 0)
{
return v_bs_917_;
}
else
{
lean_object* v_v_919_; lean_object* v_x_920_; uint8_t v_borrow_921_; lean_object* v_ty_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_936_; 
v_v_919_ = lean_array_uget(v_bs_917_, v_i_916_);
v_x_920_ = lean_ctor_get(v_v_919_, 0);
v_borrow_921_ = lean_ctor_get_uint8(v_v_919_, sizeof(void*)*2);
v_ty_922_ = lean_ctor_get(v_v_919_, 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v_v_919_);
if (v_isSharedCheck_936_ == 0)
{
v___x_924_ = v_v_919_;
v_isShared_925_ = v_isSharedCheck_936_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_ty_922_);
lean_inc(v_x_920_);
lean_dec(v_v_919_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_936_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v_bs_x27_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_926_ = lean_unsigned_to_nat(0u);
v_bs_x27_927_ = lean_array_uset(v_bs_917_, v_i_916_, v___x_926_);
v___x_928_ = l_Lean_IR_NormalizeIds_normIndex(v_x_920_, v_fst_914_);
lean_dec(v_x_920_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_928_);
v___x_930_ = v___x_924_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_928_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_ty_922_);
lean_ctor_set_uint8(v_reuseFailAlloc_935_, sizeof(void*)*2, v_borrow_921_);
v___x_930_ = v_reuseFailAlloc_935_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
size_t v___x_931_; size_t v___x_932_; lean_object* v___x_933_; 
v___x_931_ = ((size_t)1ULL);
v___x_932_ = lean_usize_add(v_i_916_, v___x_931_);
v___x_933_ = lean_array_uset(v_bs_x27_927_, v_i_916_, v___x_930_);
v_i_916_ = v___x_932_;
v_bs_917_ = v___x_933_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0___boxed(lean_object* v_fst_937_, lean_object* v_sz_938_, lean_object* v_i_939_, lean_object* v_bs_940_){
_start:
{
size_t v_sz_boxed_941_; size_t v_i_boxed_942_; lean_object* v_res_943_; 
v_sz_boxed_941_ = lean_unbox_usize(v_sz_938_);
lean_dec(v_sz_938_);
v_i_boxed_942_ = lean_unbox_usize(v_i_939_);
lean_dec(v_i_939_);
v_res_943_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(v_fst_937_, v_sz_boxed_941_, v_i_boxed_942_, v_bs_940_);
lean_dec(v_fst_937_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(lean_object* v_as_944_, size_t v_i_945_, size_t v_stop_946_, lean_object* v_b_947_, lean_object* v___y_948_){
_start:
{
uint8_t v___x_949_; 
v___x_949_ = lean_usize_dec_eq(v_i_945_, v_stop_946_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; lean_object* v_x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; size_t v___x_955_; size_t v___x_956_; 
v___x_950_ = lean_array_uget_borrowed(v_as_944_, v_i_945_);
v_x_951_ = lean_ctor_get(v___x_950_, 0);
v___x_952_ = lean_unsigned_to_nat(1u);
v___x_953_ = lean_nat_add(v___y_948_, v___x_952_);
lean_inc(v_x_951_);
v___x_954_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_x_951_, v___y_948_, v_b_947_);
v___x_955_ = ((size_t)1ULL);
v___x_956_ = lean_usize_add(v_i_945_, v___x_955_);
v_i_945_ = v___x_956_;
v_b_947_ = v___x_954_;
v___y_948_ = v___x_953_;
goto _start;
}
else
{
lean_object* v___x_958_; 
v___x_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_958_, 0, v_b_947_);
lean_ctor_set(v___x_958_, 1, v___y_948_);
return v___x_958_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1___boxed(lean_object* v_as_959_, lean_object* v_i_960_, lean_object* v_stop_961_, lean_object* v_b_962_, lean_object* v___y_963_){
_start:
{
size_t v_i_boxed_964_; size_t v_stop_boxed_965_; lean_object* v_res_966_; 
v_i_boxed_964_ = lean_unbox_usize(v_i_960_);
lean_dec(v_i_960_);
v_stop_boxed_965_ = lean_unbox_usize(v_stop_961_);
lean_dec(v_stop_961_);
v_res_966_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_as_959_, v_i_boxed_964_, v_stop_boxed_965_, v_b_962_, v___y_963_);
lean_dec_ref(v_as_959_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normFnBody(lean_object* v_x_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
switch(lean_obj_tag(v_x_967_))
{
case 0:
{
lean_object* v_x_970_; lean_object* v_ty_971_; lean_object* v_e_972_; lean_object* v_b_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_994_; 
v_x_970_ = lean_ctor_get(v_x_967_, 0);
v_ty_971_ = lean_ctor_get(v_x_967_, 1);
v_e_972_ = lean_ctor_get(v_x_967_, 2);
v_b_973_ = lean_ctor_get(v_x_967_, 3);
v_isSharedCheck_994_ = !lean_is_exclusive(v_x_967_);
if (v_isSharedCheck_994_ == 0)
{
v___x_975_ = v_x_967_;
v_isShared_976_ = v_isSharedCheck_994_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_b_973_);
lean_inc(v_e_972_);
lean_inc(v_ty_971_);
lean_inc(v_x_970_);
lean_dec(v_x_967_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_994_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_fst_981_; lean_object* v_snd_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_993_; 
v___x_977_ = lean_unsigned_to_nat(1u);
v___x_978_ = lean_nat_add(v_a_969_, v___x_977_);
lean_inc(v_a_968_);
lean_inc(v_a_969_);
v___x_979_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_x_970_, v_a_969_, v_a_968_);
v___x_980_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_973_, v___x_979_, v___x_978_);
v_fst_981_ = lean_ctor_get(v___x_980_, 0);
v_snd_982_ = lean_ctor_get(v___x_980_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_993_ == 0)
{
v___x_984_ = v___x_980_;
v_isShared_985_ = v_isSharedCheck_993_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_snd_982_);
lean_inc(v_fst_981_);
lean_dec(v___x_980_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_993_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_986_ = l_Lean_IR_NormalizeIds_normExpr(v_e_972_, v_a_968_);
lean_dec(v_a_968_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 3, v_fst_981_);
lean_ctor_set(v___x_975_, 2, v___x_986_);
lean_ctor_set(v___x_975_, 0, v_a_969_);
v___x_988_ = v___x_975_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_969_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_ty_971_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_992_, 3, v_fst_981_);
v___x_988_ = v_reuseFailAlloc_992_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_990_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_988_);
v___x_990_ = v___x_984_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_snd_982_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
case 1:
{
lean_object* v_j_995_; lean_object* v_xs_996_; lean_object* v_v_997_; lean_object* v_b_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1041_; 
v_j_995_ = lean_ctor_get(v_x_967_, 0);
v_xs_996_ = lean_ctor_get(v_x_967_, 1);
v_v_997_ = lean_ctor_get(v_x_967_, 2);
v_b_998_ = lean_ctor_get(v_x_967_, 3);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_x_967_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1000_ = v_x_967_;
v_isShared_1001_ = v_isSharedCheck_1041_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_b_998_);
lean_inc(v_v_997_);
lean_inc(v_xs_996_);
lean_inc(v_j_995_);
lean_dec(v_x_967_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1041_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v_fst_1003_; lean_object* v_snd_1004_; lean_object* v___y_1028_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1031_ = lean_unsigned_to_nat(0u);
v___x_1032_ = lean_array_get_size(v_xs_996_);
v___x_1033_ = lean_nat_dec_lt(v___x_1031_, v___x_1032_);
if (v___x_1033_ == 0)
{
lean_inc(v_a_968_);
v_fst_1003_ = v_a_968_;
v_snd_1004_ = v_a_969_;
goto v___jp_1002_;
}
else
{
uint8_t v___x_1034_; 
v___x_1034_ = lean_nat_dec_le(v___x_1032_, v___x_1032_);
if (v___x_1034_ == 0)
{
if (v___x_1033_ == 0)
{
lean_inc(v_a_968_);
v_fst_1003_ = v_a_968_;
v_snd_1004_ = v_a_969_;
goto v___jp_1002_;
}
else
{
size_t v___x_1035_; size_t v___x_1036_; lean_object* v___x_1037_; 
v___x_1035_ = ((size_t)0ULL);
v___x_1036_ = lean_usize_of_nat(v___x_1032_);
lean_inc(v_a_968_);
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_996_, v___x_1035_, v___x_1036_, v_a_968_, v_a_969_);
v___y_1028_ = v___x_1037_;
goto v___jp_1027_;
}
}
else
{
size_t v___x_1038_; size_t v___x_1039_; lean_object* v___x_1040_; 
v___x_1038_ = ((size_t)0ULL);
v___x_1039_ = lean_usize_of_nat(v___x_1032_);
lean_inc(v_a_968_);
v___x_1040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_996_, v___x_1038_, v___x_1039_, v_a_968_, v_a_969_);
v___y_1028_ = v___x_1040_;
goto v___jp_1027_;
}
}
v___jp_1002_:
{
lean_object* v___x_1005_; lean_object* v_fst_1006_; lean_object* v_snd_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v_fst_1012_; lean_object* v_snd_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1026_; 
lean_inc(v_fst_1003_);
v___x_1005_ = l_Lean_IR_NormalizeIds_normFnBody(v_v_997_, v_fst_1003_, v_snd_1004_);
v_fst_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_fst_1006_);
v_snd_1007_ = lean_ctor_get(v___x_1005_, 1);
lean_inc(v_snd_1007_);
lean_dec_ref(v___x_1005_);
v___x_1008_ = lean_unsigned_to_nat(1u);
v___x_1009_ = lean_nat_add(v_snd_1007_, v___x_1008_);
lean_inc(v_snd_1007_);
v___x_1010_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_j_995_, v_snd_1007_, v_a_968_);
v___x_1011_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_998_, v___x_1010_, v___x_1009_);
v_fst_1012_ = lean_ctor_get(v___x_1011_, 0);
v_snd_1013_ = lean_ctor_get(v___x_1011_, 1);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1015_ = v___x_1011_;
v_isShared_1016_ = v_isSharedCheck_1026_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_snd_1013_);
lean_inc(v_fst_1012_);
lean_dec(v___x_1011_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1026_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
size_t v_sz_1017_; size_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; 
v_sz_1017_ = lean_array_size(v_xs_996_);
v___x_1018_ = ((size_t)0ULL);
v___x_1019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(v_fst_1003_, v_sz_1017_, v___x_1018_, v_xs_996_);
lean_dec(v_fst_1003_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 3, v_fst_1012_);
lean_ctor_set(v___x_1000_, 2, v_fst_1006_);
lean_ctor_set(v___x_1000_, 1, v___x_1019_);
lean_ctor_set(v___x_1000_, 0, v_snd_1007_);
v___x_1021_ = v___x_1000_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_snd_1007_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1025_, 2, v_fst_1006_);
lean_ctor_set(v_reuseFailAlloc_1025_, 3, v_fst_1012_);
v___x_1021_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1023_; 
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v___x_1021_);
v___x_1023_ = v___x_1015_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_snd_1013_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
v___jp_1027_:
{
lean_object* v_fst_1029_; lean_object* v_snd_1030_; 
v_fst_1029_ = lean_ctor_get(v___y_1028_, 0);
lean_inc(v_fst_1029_);
v_snd_1030_ = lean_ctor_get(v___y_1028_, 1);
lean_inc(v_snd_1030_);
lean_dec_ref(v___y_1028_);
v_fst_1003_ = v_fst_1029_;
v_snd_1004_ = v_snd_1030_;
goto v___jp_1002_;
}
}
}
case 2:
{
lean_object* v_x_1042_; lean_object* v_i_1043_; lean_object* v_y_1044_; lean_object* v_b_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1064_; 
v_x_1042_ = lean_ctor_get(v_x_967_, 0);
v_i_1043_ = lean_ctor_get(v_x_967_, 1);
v_y_1044_ = lean_ctor_get(v_x_967_, 2);
v_b_1045_ = lean_ctor_get(v_x_967_, 3);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_x_967_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1047_ = v_x_967_;
v_isShared_1048_ = v_isSharedCheck_1064_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_b_1045_);
lean_inc(v_y_1044_);
lean_inc(v_i_1043_);
lean_inc(v_x_1042_);
lean_dec(v_x_967_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1064_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v_fst_1052_; lean_object* v_snd_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1063_; 
v___x_1049_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1042_, v_a_968_);
lean_dec(v_x_1042_);
v___x_1050_ = l_Lean_IR_NormalizeIds_normArg(v_y_1044_, v_a_968_);
v___x_1051_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1045_, v_a_968_, v_a_969_);
v_fst_1052_ = lean_ctor_get(v___x_1051_, 0);
v_snd_1053_ = lean_ctor_get(v___x_1051_, 1);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1055_ = v___x_1051_;
v_isShared_1056_ = v_isSharedCheck_1063_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_snd_1053_);
lean_inc(v_fst_1052_);
lean_dec(v___x_1051_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1063_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 3, v_fst_1052_);
lean_ctor_set(v___x_1047_, 2, v___x_1050_);
lean_ctor_set(v___x_1047_, 0, v___x_1049_);
v___x_1058_ = v___x_1047_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_i_1043_);
lean_ctor_set(v_reuseFailAlloc_1062_, 2, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1062_, 3, v_fst_1052_);
v___x_1058_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1060_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1058_);
v___x_1060_ = v___x_1055_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_snd_1053_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
case 3:
{
lean_object* v_x_1065_; lean_object* v_cidx_1066_; lean_object* v_b_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1085_; 
v_x_1065_ = lean_ctor_get(v_x_967_, 0);
v_cidx_1066_ = lean_ctor_get(v_x_967_, 1);
v_b_1067_ = lean_ctor_get(v_x_967_, 2);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_x_967_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1069_ = v_x_967_;
v_isShared_1070_ = v_isSharedCheck_1085_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_b_1067_);
lean_inc(v_cidx_1066_);
lean_inc(v_x_1065_);
lean_dec(v_x_967_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1085_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v_fst_1073_; lean_object* v_snd_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1084_; 
v___x_1071_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1065_, v_a_968_);
lean_dec(v_x_1065_);
v___x_1072_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1067_, v_a_968_, v_a_969_);
v_fst_1073_ = lean_ctor_get(v___x_1072_, 0);
v_snd_1074_ = lean_ctor_get(v___x_1072_, 1);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1076_ = v___x_1072_;
v_isShared_1077_ = v_isSharedCheck_1084_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_snd_1074_);
lean_inc(v_fst_1073_);
lean_dec(v___x_1072_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1084_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 2, v_fst_1073_);
lean_ctor_set(v___x_1069_, 0, v___x_1071_);
v___x_1079_ = v___x_1069_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_cidx_1066_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v_fst_1073_);
v___x_1079_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1081_; 
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1079_);
v___x_1081_ = v___x_1076_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_snd_1074_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
case 4:
{
lean_object* v_x_1086_; lean_object* v_i_1087_; lean_object* v_y_1088_; lean_object* v_b_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1108_; 
v_x_1086_ = lean_ctor_get(v_x_967_, 0);
v_i_1087_ = lean_ctor_get(v_x_967_, 1);
v_y_1088_ = lean_ctor_get(v_x_967_, 2);
v_b_1089_ = lean_ctor_get(v_x_967_, 3);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_x_967_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1091_ = v_x_967_;
v_isShared_1092_ = v_isSharedCheck_1108_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_b_1089_);
lean_inc(v_y_1088_);
lean_inc(v_i_1087_);
lean_inc(v_x_1086_);
lean_dec(v_x_967_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1108_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v_fst_1096_; lean_object* v_snd_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1107_; 
v___x_1093_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1086_, v_a_968_);
lean_dec(v_x_1086_);
v___x_1094_ = l_Lean_IR_NormalizeIds_normIndex(v_y_1088_, v_a_968_);
lean_dec(v_y_1088_);
v___x_1095_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1089_, v_a_968_, v_a_969_);
v_fst_1096_ = lean_ctor_get(v___x_1095_, 0);
v_snd_1097_ = lean_ctor_get(v___x_1095_, 1);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1099_ = v___x_1095_;
v_isShared_1100_ = v_isSharedCheck_1107_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_snd_1097_);
lean_inc(v_fst_1096_);
lean_dec(v___x_1095_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1107_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 3, v_fst_1096_);
lean_ctor_set(v___x_1091_, 2, v___x_1094_);
lean_ctor_set(v___x_1091_, 0, v___x_1093_);
v___x_1102_ = v___x_1091_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_i_1087_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1106_, 3, v_fst_1096_);
v___x_1102_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1104_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1102_);
v___x_1104_ = v___x_1099_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_snd_1097_);
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
}
case 5:
{
lean_object* v_x_1109_; lean_object* v_i_1110_; lean_object* v_offset_1111_; lean_object* v_y_1112_; lean_object* v_ty_1113_; lean_object* v_b_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1133_; 
v_x_1109_ = lean_ctor_get(v_x_967_, 0);
v_i_1110_ = lean_ctor_get(v_x_967_, 1);
v_offset_1111_ = lean_ctor_get(v_x_967_, 2);
v_y_1112_ = lean_ctor_get(v_x_967_, 3);
v_ty_1113_ = lean_ctor_get(v_x_967_, 4);
v_b_1114_ = lean_ctor_get(v_x_967_, 5);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_x_967_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1116_ = v_x_967_;
v_isShared_1117_ = v_isSharedCheck_1133_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_b_1114_);
lean_inc(v_ty_1113_);
lean_inc(v_y_1112_);
lean_inc(v_offset_1111_);
lean_inc(v_i_1110_);
lean_inc(v_x_1109_);
lean_dec(v_x_967_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1133_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v_fst_1121_; lean_object* v_snd_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1132_; 
v___x_1118_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1109_, v_a_968_);
lean_dec(v_x_1109_);
v___x_1119_ = l_Lean_IR_NormalizeIds_normIndex(v_y_1112_, v_a_968_);
lean_dec(v_y_1112_);
v___x_1120_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1114_, v_a_968_, v_a_969_);
v_fst_1121_ = lean_ctor_get(v___x_1120_, 0);
v_snd_1122_ = lean_ctor_get(v___x_1120_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1124_ = v___x_1120_;
v_isShared_1125_ = v_isSharedCheck_1132_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_snd_1122_);
lean_inc(v_fst_1121_);
lean_dec(v___x_1120_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1132_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 5, v_fst_1121_);
lean_ctor_set(v___x_1116_, 3, v___x_1119_);
lean_ctor_set(v___x_1116_, 0, v___x_1118_);
v___x_1127_ = v___x_1116_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_i_1110_);
lean_ctor_set(v_reuseFailAlloc_1131_, 2, v_offset_1111_);
lean_ctor_set(v_reuseFailAlloc_1131_, 3, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1131_, 4, v_ty_1113_);
lean_ctor_set(v_reuseFailAlloc_1131_, 5, v_fst_1121_);
v___x_1127_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1129_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1127_);
v___x_1129_ = v___x_1124_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_snd_1122_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
case 6:
{
lean_object* v_x_1134_; lean_object* v_n_1135_; uint8_t v_c_1136_; uint8_t v_persistent_1137_; lean_object* v_b_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1156_; 
v_x_1134_ = lean_ctor_get(v_x_967_, 0);
v_n_1135_ = lean_ctor_get(v_x_967_, 1);
v_c_1136_ = lean_ctor_get_uint8(v_x_967_, sizeof(void*)*3);
v_persistent_1137_ = lean_ctor_get_uint8(v_x_967_, sizeof(void*)*3 + 1);
v_b_1138_ = lean_ctor_get(v_x_967_, 2);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_x_967_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1140_ = v_x_967_;
v_isShared_1141_ = v_isSharedCheck_1156_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_b_1138_);
lean_inc(v_n_1135_);
lean_inc(v_x_1134_);
lean_dec(v_x_967_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1156_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v_fst_1144_; lean_object* v_snd_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1155_; 
v___x_1142_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1134_, v_a_968_);
lean_dec(v_x_1134_);
v___x_1143_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1138_, v_a_968_, v_a_969_);
v_fst_1144_ = lean_ctor_get(v___x_1143_, 0);
v_snd_1145_ = lean_ctor_get(v___x_1143_, 1);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1147_ = v___x_1143_;
v_isShared_1148_ = v_isSharedCheck_1155_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_snd_1145_);
lean_inc(v_fst_1144_);
lean_dec(v___x_1143_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1155_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 2, v_fst_1144_);
lean_ctor_set(v___x_1140_, 0, v___x_1142_);
v___x_1150_ = v___x_1140_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_n_1135_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_fst_1144_);
lean_ctor_set_uint8(v_reuseFailAlloc_1154_, sizeof(void*)*3, v_c_1136_);
lean_ctor_set_uint8(v_reuseFailAlloc_1154_, sizeof(void*)*3 + 1, v_persistent_1137_);
v___x_1150_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1152_; 
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1150_);
v___x_1152_ = v___x_1147_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_snd_1145_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
case 7:
{
lean_object* v_x_1157_; lean_object* v_n_1158_; uint8_t v_c_1159_; uint8_t v_persistent_1160_; lean_object* v_b_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1179_; 
v_x_1157_ = lean_ctor_get(v_x_967_, 0);
v_n_1158_ = lean_ctor_get(v_x_967_, 1);
v_c_1159_ = lean_ctor_get_uint8(v_x_967_, sizeof(void*)*3);
v_persistent_1160_ = lean_ctor_get_uint8(v_x_967_, sizeof(void*)*3 + 1);
v_b_1161_ = lean_ctor_get(v_x_967_, 2);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_x_967_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1163_ = v_x_967_;
v_isShared_1164_ = v_isSharedCheck_1179_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_b_1161_);
lean_inc(v_n_1158_);
lean_inc(v_x_1157_);
lean_dec(v_x_967_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1179_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v_fst_1167_; lean_object* v_snd_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1178_; 
v___x_1165_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1157_, v_a_968_);
lean_dec(v_x_1157_);
v___x_1166_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1161_, v_a_968_, v_a_969_);
v_fst_1167_ = lean_ctor_get(v___x_1166_, 0);
v_snd_1168_ = lean_ctor_get(v___x_1166_, 1);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1170_ = v___x_1166_;
v_isShared_1171_ = v_isSharedCheck_1178_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_snd_1168_);
lean_inc(v_fst_1167_);
lean_dec(v___x_1166_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1178_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 2, v_fst_1167_);
lean_ctor_set(v___x_1163_, 0, v___x_1165_);
v___x_1173_ = v___x_1163_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_n_1158_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_fst_1167_);
lean_ctor_set_uint8(v_reuseFailAlloc_1177_, sizeof(void*)*3, v_c_1159_);
lean_ctor_set_uint8(v_reuseFailAlloc_1177_, sizeof(void*)*3 + 1, v_persistent_1160_);
v___x_1173_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1175_; 
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1173_);
v___x_1175_ = v___x_1170_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_snd_1168_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
case 8:
{
lean_object* v_x_1180_; lean_object* v_b_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1199_; 
v_x_1180_ = lean_ctor_get(v_x_967_, 0);
v_b_1181_ = lean_ctor_get(v_x_967_, 1);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_x_967_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1183_ = v_x_967_;
v_isShared_1184_ = v_isSharedCheck_1199_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_b_1181_);
lean_inc(v_x_1180_);
lean_dec(v_x_967_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1199_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v_fst_1187_; lean_object* v_snd_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1198_; 
v___x_1185_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1180_, v_a_968_);
lean_dec(v_x_1180_);
v___x_1186_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1181_, v_a_968_, v_a_969_);
v_fst_1187_ = lean_ctor_get(v___x_1186_, 0);
v_snd_1188_ = lean_ctor_get(v___x_1186_, 1);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1190_ = v___x_1186_;
v_isShared_1191_ = v_isSharedCheck_1198_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_snd_1188_);
lean_inc(v_fst_1187_);
lean_dec(v___x_1186_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1198_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 1, v_fst_1187_);
lean_ctor_set(v___x_1183_, 0, v___x_1185_);
v___x_1193_ = v___x_1183_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_fst_1187_);
v___x_1193_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1195_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1193_);
v___x_1195_ = v___x_1190_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_snd_1188_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
}
case 9:
{
lean_object* v_tid_1200_; lean_object* v_x_1201_; lean_object* v_xType_1202_; lean_object* v_cs_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1223_; 
v_tid_1200_ = lean_ctor_get(v_x_967_, 0);
v_x_1201_ = lean_ctor_get(v_x_967_, 1);
v_xType_1202_ = lean_ctor_get(v_x_967_, 2);
v_cs_1203_ = lean_ctor_get(v_x_967_, 3);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_x_967_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1205_ = v_x_967_;
v_isShared_1206_ = v_isSharedCheck_1223_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_cs_1203_);
lean_inc(v_xType_1202_);
lean_inc(v_x_1201_);
lean_inc(v_tid_1200_);
lean_dec(v_x_967_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1223_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; size_t v_sz_1208_; size_t v___x_1209_; lean_object* v___x_1210_; lean_object* v_fst_1211_; lean_object* v_snd_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1222_; 
v___x_1207_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1201_, v_a_968_);
lean_dec(v_x_1201_);
v_sz_1208_ = lean_array_size(v_cs_1203_);
v___x_1209_ = ((size_t)0ULL);
v___x_1210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(v_sz_1208_, v___x_1209_, v_cs_1203_, v_a_968_, v_a_969_);
v_fst_1211_ = lean_ctor_get(v___x_1210_, 0);
v_snd_1212_ = lean_ctor_get(v___x_1210_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1214_ = v___x_1210_;
v_isShared_1215_ = v_isSharedCheck_1222_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_snd_1212_);
lean_inc(v_fst_1211_);
lean_dec(v___x_1210_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1222_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 3, v_fst_1211_);
lean_ctor_set(v___x_1205_, 1, v___x_1207_);
v___x_1217_ = v___x_1205_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_tid_1200_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v_xType_1202_);
lean_ctor_set(v_reuseFailAlloc_1221_, 3, v_fst_1211_);
v___x_1217_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1219_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1217_);
v___x_1219_ = v___x_1214_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_snd_1212_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
}
case 10:
{
lean_object* v_x_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1233_; 
v_x_1224_ = lean_ctor_get(v_x_967_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_x_967_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1226_ = v_x_967_;
v_isShared_1227_ = v_isSharedCheck_1233_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_x_1224_);
lean_dec(v_x_967_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1233_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1228_ = l_Lean_IR_NormalizeIds_normArg(v_x_1224_, v_a_968_);
lean_dec(v_a_968_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v___x_1228_);
v___x_1230_ = v___x_1226_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1231_; 
v___x_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
lean_ctor_set(v___x_1231_, 1, v_a_969_);
return v___x_1231_;
}
}
}
case 11:
{
lean_object* v_j_1234_; lean_object* v_ys_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1245_; 
v_j_1234_ = lean_ctor_get(v_x_967_, 0);
v_ys_1235_ = lean_ctor_get(v_x_967_, 1);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_x_967_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1237_ = v_x_967_;
v_isShared_1238_ = v_isSharedCheck_1245_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_ys_1235_);
lean_inc(v_j_1234_);
lean_dec(v_x_967_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1245_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1239_ = l_Lean_IR_NormalizeIds_normIndex(v_j_1234_, v_a_968_);
lean_dec(v_j_1234_);
v___x_1240_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_1235_, v_a_968_);
lean_dec(v_a_968_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 1, v___x_1240_);
lean_ctor_set(v___x_1237_, 0, v___x_1239_);
v___x_1242_ = v___x_1237_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
lean_ctor_set(v___x_1243_, 1, v_a_969_);
return v___x_1243_;
}
}
}
default: 
{
lean_object* v___x_1246_; 
lean_dec(v_a_968_);
v___x_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_x_967_);
lean_ctor_set(v___x_1246_, 1, v_a_969_);
return v___x_1246_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(size_t v_sz_1247_, size_t v_i_1248_, lean_object* v_bs_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
uint8_t v___x_1252_; 
v___x_1252_ = lean_usize_dec_lt(v_i_1248_, v_sz_1247_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
lean_dec(v___y_1250_);
v___x_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1253_, 0, v_bs_1249_);
lean_ctor_set(v___x_1253_, 1, v___y_1251_);
return v___x_1253_;
}
else
{
lean_object* v_v_1254_; lean_object* v___x_1255_; lean_object* v_bs_x27_1256_; lean_object* v_fst_1258_; lean_object* v_snd_1259_; 
v_v_1254_ = lean_array_uget(v_bs_1249_, v_i_1248_);
v___x_1255_ = lean_unsigned_to_nat(0u);
v_bs_x27_1256_ = lean_array_uset(v_bs_1249_, v_i_1248_, v___x_1255_);
if (lean_obj_tag(v_v_1254_) == 0)
{
lean_object* v_info_1264_; lean_object* v_b_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1275_; 
v_info_1264_ = lean_ctor_get(v_v_1254_, 0);
v_b_1265_ = lean_ctor_get(v_v_1254_, 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_v_1254_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1267_ = v_v_1254_;
v_isShared_1268_ = v_isSharedCheck_1275_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_b_1265_);
lean_inc(v_info_1264_);
lean_dec(v_v_1254_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1275_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; lean_object* v_fst_1270_; lean_object* v_snd_1271_; lean_object* v___x_1273_; 
lean_inc(v___y_1250_);
v___x_1269_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1265_, v___y_1250_, v___y_1251_);
v_fst_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_fst_1270_);
v_snd_1271_ = lean_ctor_get(v___x_1269_, 1);
lean_inc(v_snd_1271_);
lean_dec_ref(v___x_1269_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 1, v_fst_1270_);
v___x_1273_ = v___x_1267_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_info_1264_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_fst_1270_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
v_fst_1258_ = v___x_1273_;
v_snd_1259_ = v_snd_1271_;
goto v___jp_1257_;
}
}
}
else
{
lean_object* v_b_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1286_; 
v_b_1276_ = lean_ctor_get(v_v_1254_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_v_1254_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1278_ = v_v_1254_;
v_isShared_1279_ = v_isSharedCheck_1286_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_b_1276_);
lean_dec(v_v_1254_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1286_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v_fst_1281_; lean_object* v_snd_1282_; lean_object* v___x_1284_; 
lean_inc(v___y_1250_);
v___x_1280_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1276_, v___y_1250_, v___y_1251_);
v_fst_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_fst_1281_);
v_snd_1282_ = lean_ctor_get(v___x_1280_, 1);
lean_inc(v_snd_1282_);
lean_dec_ref(v___x_1280_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v_fst_1281_);
v___x_1284_ = v___x_1278_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_fst_1281_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
v_fst_1258_ = v___x_1284_;
v_snd_1259_ = v_snd_1282_;
goto v___jp_1257_;
}
}
}
v___jp_1257_:
{
size_t v___x_1260_; size_t v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = ((size_t)1ULL);
v___x_1261_ = lean_usize_add(v_i_1248_, v___x_1260_);
v___x_1262_ = lean_array_uset(v_bs_x27_1256_, v_i_1248_, v_fst_1258_);
v_i_1248_ = v___x_1261_;
v_bs_1249_ = v___x_1262_;
v___y_1251_ = v_snd_1259_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2___boxed(lean_object* v_sz_1287_, lean_object* v_i_1288_, lean_object* v_bs_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
size_t v_sz_boxed_1292_; size_t v_i_boxed_1293_; lean_object* v_res_1294_; 
v_sz_boxed_1292_ = lean_unbox_usize(v_sz_1287_);
lean_dec(v_sz_1287_);
v_i_boxed_1293_ = lean_unbox_usize(v_i_1288_);
lean_dec(v_i_1288_);
v_res_1294_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(v_sz_boxed_1292_, v_i_boxed_1293_, v_bs_1289_, v___y_1290_, v___y_1291_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normDecl(lean_object* v_d_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
if (lean_obj_tag(v_d_1295_) == 0)
{
lean_object* v_xs_1298_; lean_object* v_body_1299_; lean_object* v_fst_1301_; lean_object* v_snd_1302_; lean_object* v___y_1315_; lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
v_xs_1298_ = lean_ctor_get(v_d_1295_, 1);
v_body_1299_ = lean_ctor_get(v_d_1295_, 3);
v___x_1318_ = lean_unsigned_to_nat(0u);
v___x_1319_ = lean_array_get_size(v_xs_1298_);
v___x_1320_ = lean_nat_dec_lt(v___x_1318_, v___x_1319_);
if (v___x_1320_ == 0)
{
v_fst_1301_ = v_a_1296_;
v_snd_1302_ = v_a_1297_;
goto v___jp_1300_;
}
else
{
uint8_t v___x_1321_; 
v___x_1321_ = lean_nat_dec_le(v___x_1319_, v___x_1319_);
if (v___x_1321_ == 0)
{
if (v___x_1320_ == 0)
{
v_fst_1301_ = v_a_1296_;
v_snd_1302_ = v_a_1297_;
goto v___jp_1300_;
}
else
{
size_t v___x_1322_; size_t v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = ((size_t)0ULL);
v___x_1323_ = lean_usize_of_nat(v___x_1319_);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_1298_, v___x_1322_, v___x_1323_, v_a_1296_, v_a_1297_);
v___y_1315_ = v___x_1324_;
goto v___jp_1314_;
}
}
else
{
size_t v___x_1325_; size_t v___x_1326_; lean_object* v___x_1327_; 
v___x_1325_ = ((size_t)0ULL);
v___x_1326_ = lean_usize_of_nat(v___x_1319_);
v___x_1327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_1298_, v___x_1325_, v___x_1326_, v_a_1296_, v_a_1297_);
v___y_1315_ = v___x_1327_;
goto v___jp_1314_;
}
}
v___jp_1300_:
{
lean_object* v___x_1303_; lean_object* v_fst_1304_; lean_object* v_snd_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1313_; 
lean_inc(v_body_1299_);
v___x_1303_ = l_Lean_IR_NormalizeIds_normFnBody(v_body_1299_, v_fst_1301_, v_snd_1302_);
v_fst_1304_ = lean_ctor_get(v___x_1303_, 0);
v_snd_1305_ = lean_ctor_get(v___x_1303_, 1);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1307_ = v___x_1303_;
v_isShared_1308_ = v_isSharedCheck_1313_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_snd_1305_);
lean_inc(v_fst_1304_);
lean_dec(v___x_1303_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1313_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; lean_object* v___x_1311_; 
v___x_1309_ = l_Lean_IR_Decl_updateBody_x21(v_d_1295_, v_fst_1304_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v___x_1309_);
v___x_1311_ = v___x_1307_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_snd_1305_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
v___jp_1314_:
{
lean_object* v_fst_1316_; lean_object* v_snd_1317_; 
v_fst_1316_ = lean_ctor_get(v___y_1315_, 0);
lean_inc(v_fst_1316_);
v_snd_1317_ = lean_ctor_get(v___y_1315_, 1);
lean_inc(v_snd_1317_);
lean_dec_ref(v___y_1315_);
v_fst_1301_ = v_fst_1316_;
v_snd_1302_ = v_snd_1317_;
goto v___jp_1300_;
}
}
else
{
lean_object* v___x_1328_; 
lean_dec(v_a_1296_);
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v_d_1295_);
lean_ctor_set(v___x_1328_, 1, v_a_1297_);
return v___x_1328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_normalizeIds(lean_object* v_d_1329_){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v_fst_1333_; 
v___x_1330_ = lean_box(1);
v___x_1331_ = lean_unsigned_to_nat(1u);
v___x_1332_ = l_Lean_IR_NormalizeIds_normDecl(v_d_1329_, v___x_1330_, v___x_1331_);
v_fst_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_fst_1333_);
lean_dec_ref(v___x_1332_);
return v_fst_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArg(lean_object* v_f_1334_, lean_object* v_x_1335_){
_start:
{
if (lean_obj_tag(v_x_1335_) == 0)
{
lean_object* v_id_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1344_; 
v_id_1336_ = lean_ctor_get(v_x_1335_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_x_1335_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1338_ = v_x_1335_;
v_isShared_1339_ = v_isSharedCheck_1344_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_id_1336_);
lean_dec(v_x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1344_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1340_ = lean_apply_1(v_f_1334_, v_id_1336_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1340_);
v___x_1342_ = v___x_1338_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
else
{
lean_dec_ref(v_f_1334_);
return v_x_1335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(lean_object* v_f_1345_, size_t v_sz_1346_, size_t v_i_1347_, lean_object* v_bs_1348_){
_start:
{
uint8_t v___x_1349_; 
v___x_1349_ = lean_usize_dec_lt(v_i_1347_, v_sz_1346_);
if (v___x_1349_ == 0)
{
lean_dec_ref(v_f_1345_);
return v_bs_1348_;
}
else
{
lean_object* v_v_1350_; lean_object* v___x_1351_; lean_object* v_bs_x27_1352_; lean_object* v___y_1354_; 
v_v_1350_ = lean_array_uget(v_bs_1348_, v_i_1347_);
v___x_1351_ = lean_unsigned_to_nat(0u);
v_bs_x27_1352_ = lean_array_uset(v_bs_1348_, v_i_1347_, v___x_1351_);
if (lean_obj_tag(v_v_1350_) == 0)
{
lean_object* v_id_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1367_; 
v_id_1359_ = lean_ctor_get(v_v_1350_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_v_1350_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1361_ = v_v_1350_;
v_isShared_1362_ = v_isSharedCheck_1367_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_id_1359_);
lean_dec(v_v_1350_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1367_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v___x_1365_; 
lean_inc_ref(v_f_1345_);
v___x_1363_ = lean_apply_1(v_f_1345_, v_id_1359_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1363_);
v___x_1365_ = v___x_1361_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
v___y_1354_ = v___x_1365_;
goto v___jp_1353_;
}
}
}
else
{
v___y_1354_ = v_v_1350_;
goto v___jp_1353_;
}
v___jp_1353_:
{
size_t v___x_1355_; size_t v___x_1356_; lean_object* v___x_1357_; 
v___x_1355_ = ((size_t)1ULL);
v___x_1356_ = lean_usize_add(v_i_1347_, v___x_1355_);
v___x_1357_ = lean_array_uset(v_bs_x27_1352_, v_i_1347_, v___y_1354_);
v_i_1347_ = v___x_1356_;
v_bs_1348_ = v___x_1357_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0___boxed(lean_object* v_f_1368_, lean_object* v_sz_1369_, lean_object* v_i_1370_, lean_object* v_bs_1371_){
_start:
{
size_t v_sz_boxed_1372_; size_t v_i_boxed_1373_; lean_object* v_res_1374_; 
v_sz_boxed_1372_ = lean_unbox_usize(v_sz_1369_);
lean_dec(v_sz_1369_);
v_i_boxed_1373_ = lean_unbox_usize(v_i_1370_);
lean_dec(v_i_1370_);
v_res_1374_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(v_f_1368_, v_sz_boxed_1372_, v_i_boxed_1373_, v_bs_1371_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArgs(lean_object* v_f_1375_, lean_object* v_as_1376_){
_start:
{
size_t v_sz_1377_; size_t v___x_1378_; lean_object* v___x_1379_; 
v_sz_1377_ = lean_array_size(v_as_1376_);
v___x_1378_ = ((size_t)0ULL);
v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(v_f_1375_, v_sz_1377_, v___x_1378_, v_as_1376_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapExpr(lean_object* v_f_1380_, lean_object* v_x_1381_){
_start:
{
switch(lean_obj_tag(v_x_1381_))
{
case 0:
{
lean_object* v_i_1382_; lean_object* v_ys_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1391_; 
v_i_1382_ = lean_ctor_get(v_x_1381_, 0);
v_ys_1383_ = lean_ctor_get(v_x_1381_, 1);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_x_1381_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1385_ = v_x_1381_;
v_isShared_1386_ = v_isSharedCheck_1391_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_ys_1383_);
lean_inc(v_i_1382_);
lean_dec(v_x_1381_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1391_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1387_ = l_Lean_IR_MapVars_mapArgs(v_f_1380_, v_ys_1383_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 1, v___x_1387_);
v___x_1389_ = v___x_1385_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_i_1382_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
case 1:
{
lean_object* v_n_1392_; lean_object* v_x_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1401_; 
v_n_1392_ = lean_ctor_get(v_x_1381_, 0);
v_x_1393_ = lean_ctor_get(v_x_1381_, 1);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_x_1381_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1395_ = v_x_1381_;
v_isShared_1396_ = v_isSharedCheck_1401_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_x_1393_);
lean_inc(v_n_1392_);
lean_dec(v_x_1381_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1401_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1397_ = lean_apply_1(v_f_1380_, v_x_1393_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 1, v___x_1397_);
v___x_1399_ = v___x_1395_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_n_1392_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
case 2:
{
lean_object* v_x_1402_; lean_object* v_i_1403_; uint8_t v_updtHeader_1404_; lean_object* v_ys_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1414_; 
v_x_1402_ = lean_ctor_get(v_x_1381_, 0);
v_i_1403_ = lean_ctor_get(v_x_1381_, 1);
v_updtHeader_1404_ = lean_ctor_get_uint8(v_x_1381_, sizeof(void*)*3);
v_ys_1405_ = lean_ctor_get(v_x_1381_, 2);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_x_1381_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1407_ = v_x_1381_;
v_isShared_1408_ = v_isSharedCheck_1414_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_ys_1405_);
lean_inc(v_i_1403_);
lean_inc(v_x_1402_);
lean_dec(v_x_1381_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1414_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
lean_inc_ref(v_f_1380_);
v___x_1409_ = lean_apply_1(v_f_1380_, v_x_1402_);
v___x_1410_ = l_Lean_IR_MapVars_mapArgs(v_f_1380_, v_ys_1405_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 2, v___x_1410_);
lean_ctor_set(v___x_1407_, 0, v___x_1409_);
v___x_1412_ = v___x_1407_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_i_1403_);
lean_ctor_set(v_reuseFailAlloc_1413_, 2, v___x_1410_);
lean_ctor_set_uint8(v_reuseFailAlloc_1413_, sizeof(void*)*3, v_updtHeader_1404_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
case 3:
{
lean_object* v_i_1415_; lean_object* v_x_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1424_; 
v_i_1415_ = lean_ctor_get(v_x_1381_, 0);
v_x_1416_ = lean_ctor_get(v_x_1381_, 1);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_x_1381_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1418_ = v_x_1381_;
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_x_1416_);
lean_inc(v_i_1415_);
lean_dec(v_x_1381_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1420_ = lean_apply_1(v_f_1380_, v_x_1416_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v___x_1420_);
v___x_1422_ = v___x_1418_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_i_1415_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
case 4:
{
lean_object* v_i_1425_; lean_object* v_x_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1434_; 
v_i_1425_ = lean_ctor_get(v_x_1381_, 0);
v_x_1426_ = lean_ctor_get(v_x_1381_, 1);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_x_1381_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1428_ = v_x_1381_;
v_isShared_1429_ = v_isSharedCheck_1434_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_x_1426_);
lean_inc(v_i_1425_);
lean_dec(v_x_1381_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1434_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1430_ = lean_apply_1(v_f_1380_, v_x_1426_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 1, v___x_1430_);
v___x_1432_ = v___x_1428_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_i_1425_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
case 5:
{
lean_object* v_n_1435_; lean_object* v_offset_1436_; lean_object* v_x_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1445_; 
v_n_1435_ = lean_ctor_get(v_x_1381_, 0);
v_offset_1436_ = lean_ctor_get(v_x_1381_, 1);
v_x_1437_ = lean_ctor_get(v_x_1381_, 2);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_x_1381_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1439_ = v_x_1381_;
v_isShared_1440_ = v_isSharedCheck_1445_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_x_1437_);
lean_inc(v_offset_1436_);
lean_inc(v_n_1435_);
lean_dec(v_x_1381_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1445_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1441_ = lean_apply_1(v_f_1380_, v_x_1437_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 2, v___x_1441_);
v___x_1443_ = v___x_1439_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_n_1435_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_offset_1436_);
lean_ctor_set(v_reuseFailAlloc_1444_, 2, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
case 6:
{
lean_object* v_c_1446_; lean_object* v_ys_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1455_; 
v_c_1446_ = lean_ctor_get(v_x_1381_, 0);
v_ys_1447_ = lean_ctor_get(v_x_1381_, 1);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_x_1381_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1449_ = v_x_1381_;
v_isShared_1450_ = v_isSharedCheck_1455_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_ys_1447_);
lean_inc(v_c_1446_);
lean_dec(v_x_1381_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1455_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1451_ = l_Lean_IR_MapVars_mapArgs(v_f_1380_, v_ys_1447_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 1, v___x_1451_);
v___x_1453_ = v___x_1449_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_c_1446_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
case 7:
{
lean_object* v_c_1456_; lean_object* v_ys_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1465_; 
v_c_1456_ = lean_ctor_get(v_x_1381_, 0);
v_ys_1457_ = lean_ctor_get(v_x_1381_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_x_1381_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1459_ = v_x_1381_;
v_isShared_1460_ = v_isSharedCheck_1465_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_ys_1457_);
lean_inc(v_c_1456_);
lean_dec(v_x_1381_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1465_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v___x_1463_; 
v___x_1461_ = l_Lean_IR_MapVars_mapArgs(v_f_1380_, v_ys_1457_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 1, v___x_1461_);
v___x_1463_ = v___x_1459_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_c_1456_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v___x_1461_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
case 8:
{
lean_object* v_x_1466_; lean_object* v_ys_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1476_; 
v_x_1466_ = lean_ctor_get(v_x_1381_, 0);
v_ys_1467_ = lean_ctor_get(v_x_1381_, 1);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_x_1381_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1469_ = v_x_1381_;
v_isShared_1470_ = v_isSharedCheck_1476_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_ys_1467_);
lean_inc(v_x_1466_);
lean_dec(v_x_1381_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1476_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1474_; 
lean_inc_ref(v_f_1380_);
v___x_1471_ = lean_apply_1(v_f_1380_, v_x_1466_);
v___x_1472_ = l_Lean_IR_MapVars_mapArgs(v_f_1380_, v_ys_1467_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 1, v___x_1472_);
lean_ctor_set(v___x_1469_, 0, v___x_1471_);
v___x_1474_ = v___x_1469_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
case 9:
{
lean_object* v_ty_1477_; lean_object* v_x_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1486_; 
v_ty_1477_ = lean_ctor_get(v_x_1381_, 0);
v_x_1478_ = lean_ctor_get(v_x_1381_, 1);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_x_1381_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1480_ = v_x_1381_;
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_x_1478_);
lean_inc(v_ty_1477_);
lean_dec(v_x_1381_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1482_ = lean_apply_1(v_f_1380_, v_x_1478_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v___x_1482_);
v___x_1484_ = v___x_1480_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_ty_1477_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
case 10:
{
lean_object* v_x_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1495_; 
v_x_1487_ = lean_ctor_get(v_x_1381_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_x_1381_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1489_ = v_x_1381_;
v_isShared_1490_ = v_isSharedCheck_1495_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_x_1487_);
lean_dec(v_x_1381_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1495_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1491_ = lean_apply_1(v_f_1380_, v_x_1487_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v___x_1491_);
v___x_1493_ = v___x_1489_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
case 11:
{
lean_dec_ref(v_f_1380_);
return v_x_1381_;
}
default: 
{
lean_object* v_x_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1504_; 
v_x_1496_ = lean_ctor_get(v_x_1381_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_x_1381_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1498_ = v_x_1381_;
v_isShared_1499_ = v_isSharedCheck_1504_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_x_1496_);
lean_dec(v_x_1381_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1504_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1500_ = lean_apply_1(v_f_1380_, v_x_1496_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 0, v___x_1500_);
v___x_1502_ = v___x_1498_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapFnBody(lean_object* v_f_1505_, lean_object* v_x_1506_){
_start:
{
switch(lean_obj_tag(v_x_1506_))
{
case 0:
{
lean_object* v_x_1507_; lean_object* v_ty_1508_; lean_object* v_e_1509_; lean_object* v_b_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1519_; 
v_x_1507_ = lean_ctor_get(v_x_1506_, 0);
v_ty_1508_ = lean_ctor_get(v_x_1506_, 1);
v_e_1509_ = lean_ctor_get(v_x_1506_, 2);
v_b_1510_ = lean_ctor_get(v_x_1506_, 3);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_x_1506_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1512_ = v_x_1506_;
v_isShared_1513_ = v_isSharedCheck_1519_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_b_1510_);
lean_inc(v_e_1509_);
lean_inc(v_ty_1508_);
lean_inc(v_x_1507_);
lean_dec(v_x_1506_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1519_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1517_; 
lean_inc_ref(v_f_1505_);
v___x_1514_ = l_Lean_IR_MapVars_mapExpr(v_f_1505_, v_e_1509_);
v___x_1515_ = l_Lean_IR_MapVars_mapFnBody(v_f_1505_, v_b_1510_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 3, v___x_1515_);
lean_ctor_set(v___x_1512_, 2, v___x_1514_);
v___x_1517_ = v___x_1512_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_x_1507_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_ty_1508_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
case 1:
{
lean_object* v_j_1520_; lean_object* v_xs_1521_; lean_object* v_v_1522_; lean_object* v_b_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1532_; 
v_j_1520_ = lean_ctor_get(v_x_1506_, 0);
v_xs_1521_ = lean_ctor_get(v_x_1506_, 1);
v_v_1522_ = lean_ctor_get(v_x_1506_, 2);
v_b_1523_ = lean_ctor_get(v_x_1506_, 3);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_x_1506_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1525_ = v_x_1506_;
v_isShared_1526_ = v_isSharedCheck_1532_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_b_1523_);
lean_inc(v_v_1522_);
lean_inc(v_xs_1521_);
lean_inc(v_j_1520_);
lean_dec(v_x_1506_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1532_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; 
lean_inc_ref(v_f_1505_);
v___x_1527_ = l_Lean_IR_MapVars_mapFnBody(v_f_1505_, v_v_1522_);
v___x_1528_ = l_Lean_IR_MapVars_mapFnBody(v_f_1505_, v_b_1523_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 3, v___x_1528_);
lean_ctor_set(v___x_1525_, 2, v___x_1527_);
v___x_1530_ = v___x_1525_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_j_1520_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_xs_1521_);
lean_ctor_set(v_reuseFailAlloc_1531_, 2, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1531_, 3, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
case 2:
{
lean_object* v_x_1533_; lean_object* v_i_1534_; lean_object* v_y_1535_; lean_object* v_b_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1556_; 
v_x_1533_ = lean_ctor_get(v_x_1506_, 0);
v_i_1534_ = lean_ctor_get(v_x_1506_, 1);
v_y_1535_ = lean_ctor_get(v_x_1506_, 2);
v_b_1536_ = lean_ctor_get(v_x_1506_, 3);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_x_1506_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1538_ = v_x_1506_;
v_isShared_1539_ = v_isSharedCheck_1556_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_b_1536_);
lean_inc(v_y_1535_);
lean_inc(v_i_1534_);
lean_inc(v_x_1533_);
lean_dec(v_x_1506_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1556_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___y_1542_; 
lean_inc_ref(v_f_1505_);
v___x_1540_ = lean_apply_1(v_f_1505_, v_x_1533_);
if (lean_obj_tag(v_y_1535_) == 0)
{
lean_object* v_id_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1555_; 
v_id_1547_ = lean_ctor_get(v_y_1535_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_y_1535_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1549_ = v_y_1535_;
v_isShared_1550_ = v_isSharedCheck_1555_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_id_1547_);
lean_dec(v_y_1535_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1555_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; lean_object* v___x_1553_; 
lean_inc_ref(v_f_1505_);
v___x_1551_ = lean_apply_1(v_f_1505_, v_id_1547_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1551_);
v___x_1553_ = v___x_1549_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
v___y_1542_ = v___x_1553_;
goto v___jp_1541_;
}
}
}
else
{
v___y_1542_ = v_y_1535_;
goto v___jp_1541_;
}
v___jp_1541_:
{
lean_object* v___x_1543_; lean_object* v___x_1545_; 
v___x_1543_ = l_Lean_IR_MapVars_mapFnBody(v_f_1505_, v_b_1536_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 3, v___x_1543_);
lean_ctor_set(v___x_1538_, 2, v___y_1542_);
lean_ctor_set(v___x_1538_, 0, v___x_1540_);
v___x_1545_ = v___x_1538_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_i_1534_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v___y_1542_);
lean_ctor_set(v_reuseFailAlloc_1546_, 3, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
case 3:
{
lean_object* v_x_1557_; lean_object* v_cidx_1558_; lean_object* v_b_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1568_; 
v_x_1557_ = lean_ctor_get(v_x_1506_, 0);
v_cidx_1558_ = lean_ctor_get(v_x_1506_, 1);
v_b_1559_ = lean_ctor_get(v_x_1506_, 2);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_x_1506_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1561_ = v_x_1506_;
v_isShared_1562_ = v_isSharedCheck_1568_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_b_1559_);
lean_inc(v_cidx_1558_);
lean_inc(v_x_1557_);
lean_dec(v_x_1506_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1568_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
lean_inc_ref(v_f_1505_);
v___x_1563_ = lean_apply_1(v_f_1505_, v_x_1557_);
v___x_1564_ = l_Lean_IR_MapVars_mapFnBody(v_f_1505_, v_b_1559_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 2, v___x_1564_);
lean_ctor_set(v___x_1561_, 0, v___x_1563_);
v___x_1566_ = v___x_1561_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_cidx_1558_);
lean_ctor_set(v_reuseFailAlloc_1567_, 2, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
case 4:
{
lean_object* v_x_1569_; lean_object* v_i_1570_; lean_object* v_y_1571_; lean_object* v_b_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1582_; 
v_x_1569_ = lean_ctor_get(v_x_1506_, 0);
v_i_1570_ = lean_ctor_get(v_x_1506_, 1);
v_y_1571_ = lean_ctor_get(v_x_1506_, 2);
v_b_1572_ = lean_ctor_get(v_x_1506_, 3);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_x_1506_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1574_ = v_x_1506_;
v_isShared_1575_ = v_isSharedCheck_1582_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_b_1572_);
lean_inc(v_y_1571_);
lean_inc(v_i_1570_);
lean_inc(v_x_1569_);
lean_dec(v_x_1506_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1582_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
lean_inc_ref(v_f_1505_);
v___x_1576_ = lean_apply_1(v_f_1505_, v_x_1569_);
lean_inc_ref(v_f_1505_);
v___x_1577_ = lean_apply_1(v_f_1505_, v_y_1571_);
v___x_1578_ = l_Lean_IR_MapVars_mapFnBody(v_f_1505_, v_b_1572_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 3, v___x_1578_);
lean_ctor_set(v___x_1574_, 2, v___x_1577_);
lean_ctor_set(v___x_1574_, 0, v___x_1576_);
v___x_1580_ = v___x_1574_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_i_1570_);
lean_ctor_set(v_reuseFailAlloc_1581_, 2, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1581_, 3, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
case 5:
{
lean_object* v_x_1583_; lean_object* v_i_1584_; lean_object* v_offset_1585_; lean_object* v_y_1586_; lean_object* v_ty_1587_; lean_object* v_b_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1598_; 
v_x_1583_ = lean_ctor_get(v_x_1506_, 0);
v_i_1584_ = lean_ctor_get(v_x_1506_, 1);
v_offset_1585_ = lean_ctor_get(v_x_1506_, 2);
v_y_1586_ = lean_ctor_get(v_x_1506_, 3);
v_ty_1587_ = lean_ctor_get(v_x_1506_, 4);
v_b_1588_ = lean_ctor_get(v_x_1506_, 5);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_x_1506_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1590_ = v_x_1506_;
v_isShared_1591_ = v_isSharedCheck_1598_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_b_1588_);
lean_inc(v_ty_1587_);
lean_inc(v_y_1586_);
lean_inc(v_offset_1585_);
lean_inc(v_i_1584_);
lean_inc(v_x_1583_);
lean_dec(v_x_1506_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1598_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1596_; 
lean_inc_ref(v_f_1505_);
v___x_1592_ = lean_apply_1(v_f_1505_, v_x_1583_);
lean_inc_ref(v_f_1505_);
v___x_1593_ = lean_apply_1(v_f_1505_, v_y_1586_);
v___x_1594_ = l_Lean_IR_MapVars_mapFnBody(v_f_1505_, v_b_1588_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 5, v___x_1594_);
lean_ctor_set(v___x_1590_, 3, v___x_1593_);
lean_ctor_set(v___x_1590_, 0, v___x_1592_);
v___x_1596_ = v___x_1590_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1592_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_i_1584_);
lean_ctor_set(v_reuseFailAlloc_1597_, 2, v_offset_1585_);
lean_ctor_set(v_reuseFailAlloc_1597_, 3, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1597_, 4, v_ty_1587_);
lean_ctor_set(v_reuseFailAlloc_1597_, 5, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
case 6:
{
lean_object* v_x_1599_; lean_object* v_n_1600_; uint8_t v_c_1601_; uint8_t v_persistent_1602_; lean_object* v_b_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1612_; 
v_x_1599_ = lean_ctor_get(v_x_1506_, 0);
v_n_1600_ = lean_ctor_get(v_x_1506_, 1);
v_c_1601_ = lean_ctor_get_uint8(v_x_1506_, sizeof(void*)*3);
v_persistent_1602_ = lean_ctor_get_uint8(v_x_1506_, sizeof(void*)*3 + 1);
v_b_1603_ = lean_ctor_get(v_x_1506_, 2);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_x_1506_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1605_ = v_x_1506_;
v_isShared_1606_ = v_isSharedCheck_1612_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_b_1603_);
lean_inc(v_n_1600_);
lean_inc(v_x_1599_);
lean_dec(v_x_1506_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1612_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1610_; 
lean_inc_ref(v_f_1505_);
v___x_1607_ = lean_apply_1(v_f_1505_, v_x_1599_);
v___x_1608_ = l_Lean_IR_MapVars_mapFnBody(v_f_1505_, v_b_1603_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 2, v___x_1608_);
lean_ctor_set(v___x_1605_, 0, v___x_1607_);
v___x_1610_ = v___x_1605_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_n_1600_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v___x_1608_);
lean_ctor_set_uint8(v_reuseFailAlloc_1611_, sizeof(void*)*3, v_c_1601_);
lean_ctor_set_uint8(v_reuseFailAlloc_1611_, sizeof(void*)*3 + 1, v_persistent_1602_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
case 7:
{
lean_object* v_x_1613_; lean_object* v_n_1614_; uint8_t v_c_1615_; uint8_t v_persistent_1616_; lean_object* v_b_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1626_; 
v_x_1613_ = lean_ctor_get(v_x_1506_, 0);
v_n_1614_ = lean_ctor_get(v_x_1506_, 1);
v_c_1615_ = lean_ctor_get_uint8(v_x_1506_, sizeof(void*)*3);
v_persistent_1616_ = lean_ctor_get_uint8(v_x_1506_, sizeof(void*)*3 + 1);
v_b_1617_ = lean_ctor_get(v_x_1506_, 2);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_x_1506_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1619_ = v_x_1506_;
v_isShared_1620_ = v_isSharedCheck_1626_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_b_1617_);
lean_inc(v_n_1614_);
lean_inc(v_x_1613_);
lean_dec(v_x_1506_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1626_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1624_; 
lean_inc_ref(v_f_1505_);
v___x_1621_ = lean_apply_1(v_f_1505_, v_x_1613_);
v___x_1622_ = l_Lean_IR_MapVars_mapFnBody(v_f_1505_, v_b_1617_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 2, v___x_1622_);
lean_ctor_set(v___x_1619_, 0, v___x_1621_);
v___x_1624_ = v___x_1619_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_n_1614_);
lean_ctor_set(v_reuseFailAlloc_1625_, 2, v___x_1622_);
lean_ctor_set_uint8(v_reuseFailAlloc_1625_, sizeof(void*)*3, v_c_1615_);
lean_ctor_set_uint8(v_reuseFailAlloc_1625_, sizeof(void*)*3 + 1, v_persistent_1616_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
case 8:
{
lean_object* v_x_1627_; lean_object* v_b_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1637_; 
v_x_1627_ = lean_ctor_get(v_x_1506_, 0);
v_b_1628_ = lean_ctor_get(v_x_1506_, 1);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_x_1506_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1630_ = v_x_1506_;
v_isShared_1631_ = v_isSharedCheck_1637_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_b_1628_);
lean_inc(v_x_1627_);
lean_dec(v_x_1506_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1637_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; 
lean_inc_ref(v_f_1505_);
v___x_1632_ = lean_apply_1(v_f_1505_, v_x_1627_);
v___x_1633_ = l_Lean_IR_MapVars_mapFnBody(v_f_1505_, v_b_1628_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 1, v___x_1633_);
lean_ctor_set(v___x_1630_, 0, v___x_1632_);
v___x_1635_ = v___x_1630_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
case 9:
{
lean_object* v_tid_1638_; lean_object* v_x_1639_; lean_object* v_xType_1640_; lean_object* v_cs_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1652_; 
v_tid_1638_ = lean_ctor_get(v_x_1506_, 0);
v_x_1639_ = lean_ctor_get(v_x_1506_, 1);
v_xType_1640_ = lean_ctor_get(v_x_1506_, 2);
v_cs_1641_ = lean_ctor_get(v_x_1506_, 3);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_x_1506_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1643_ = v_x_1506_;
v_isShared_1644_ = v_isSharedCheck_1652_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_cs_1641_);
lean_inc(v_xType_1640_);
lean_inc(v_x_1639_);
lean_inc(v_tid_1638_);
lean_dec(v_x_1506_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1652_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; size_t v_sz_1646_; size_t v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1650_; 
lean_inc_ref(v_f_1505_);
v___x_1645_ = lean_apply_1(v_f_1505_, v_x_1639_);
v_sz_1646_ = lean_array_size(v_cs_1641_);
v___x_1647_ = ((size_t)0ULL);
v___x_1648_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(v_f_1505_, v_sz_1646_, v___x_1647_, v_cs_1641_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 3, v___x_1648_);
lean_ctor_set(v___x_1643_, 1, v___x_1645_);
v___x_1650_ = v___x_1643_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_tid_1638_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v___x_1645_);
lean_ctor_set(v_reuseFailAlloc_1651_, 2, v_xType_1640_);
lean_ctor_set(v_reuseFailAlloc_1651_, 3, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
case 10:
{
lean_object* v_x_1653_; 
v_x_1653_ = lean_ctor_get(v_x_1506_, 0);
lean_inc(v_x_1653_);
if (lean_obj_tag(v_x_1653_) == 0)
{
lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1669_; 
v_isSharedCheck_1669_ = !lean_is_exclusive(v_x_1506_);
if (v_isSharedCheck_1669_ == 0)
{
lean_object* v_unused_1670_; 
v_unused_1670_ = lean_ctor_get(v_x_1506_, 0);
lean_dec(v_unused_1670_);
v___x_1655_ = v_x_1506_;
v_isShared_1656_ = v_isSharedCheck_1669_;
goto v_resetjp_1654_;
}
else
{
lean_dec(v_x_1506_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1669_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v_id_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1668_; 
v_id_1657_ = lean_ctor_get(v_x_1653_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_x_1653_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1659_ = v_x_1653_;
v_isShared_1660_ = v_isSharedCheck_1668_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_id_1657_);
lean_dec(v_x_1653_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1668_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1661_ = lean_apply_1(v_f_1505_, v_id_1657_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v___x_1661_);
v___x_1663_ = v___x_1659_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1665_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1663_);
v___x_1665_ = v___x_1655_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_1505_);
return v_x_1506_;
}
}
case 11:
{
lean_object* v_j_1671_; lean_object* v_ys_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1680_; 
v_j_1671_ = lean_ctor_get(v_x_1506_, 0);
v_ys_1672_ = lean_ctor_get(v_x_1506_, 1);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_x_1506_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1674_ = v_x_1506_;
v_isShared_1675_ = v_isSharedCheck_1680_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_ys_1672_);
lean_inc(v_j_1671_);
lean_dec(v_x_1506_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1680_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1676_ = l_Lean_IR_MapVars_mapArgs(v_f_1505_, v_ys_1672_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 1, v___x_1676_);
v___x_1678_ = v___x_1674_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_j_1671_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
default: 
{
lean_dec_ref(v_f_1505_);
return v_x_1506_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(lean_object* v_f_1681_, size_t v_sz_1682_, size_t v_i_1683_, lean_object* v_bs_1684_){
_start:
{
uint8_t v___x_1685_; 
v___x_1685_ = lean_usize_dec_lt(v_i_1683_, v_sz_1682_);
if (v___x_1685_ == 0)
{
lean_dec_ref(v_f_1681_);
return v_bs_1684_;
}
else
{
lean_object* v_v_1686_; lean_object* v___x_1687_; lean_object* v_bs_x27_1688_; lean_object* v___y_1690_; 
v_v_1686_ = lean_array_uget(v_bs_1684_, v_i_1683_);
v___x_1687_ = lean_unsigned_to_nat(0u);
v_bs_x27_1688_ = lean_array_uset(v_bs_1684_, v_i_1683_, v___x_1687_);
if (lean_obj_tag(v_v_1686_) == 0)
{
lean_object* v_info_1695_; lean_object* v_b_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1704_; 
v_info_1695_ = lean_ctor_get(v_v_1686_, 0);
v_b_1696_ = lean_ctor_get(v_v_1686_, 1);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_v_1686_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1698_ = v_v_1686_;
v_isShared_1699_ = v_isSharedCheck_1704_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_b_1696_);
lean_inc(v_info_1695_);
lean_dec(v_v_1686_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1704_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1702_; 
lean_inc_ref(v_f_1681_);
v___x_1700_ = l_Lean_IR_MapVars_mapFnBody(v_f_1681_, v_b_1696_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 1, v___x_1700_);
v___x_1702_ = v___x_1698_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_info_1695_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
v___y_1690_ = v___x_1702_;
goto v___jp_1689_;
}
}
}
else
{
lean_object* v_b_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1713_; 
v_b_1705_ = lean_ctor_get(v_v_1686_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_v_1686_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1707_ = v_v_1686_;
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_b_1705_);
lean_dec(v_v_1686_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1711_; 
lean_inc_ref(v_f_1681_);
v___x_1709_ = l_Lean_IR_MapVars_mapFnBody(v_f_1681_, v_b_1705_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1709_);
v___x_1711_ = v___x_1707_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
v___y_1690_ = v___x_1711_;
goto v___jp_1689_;
}
}
}
v___jp_1689_:
{
size_t v___x_1691_; size_t v___x_1692_; lean_object* v___x_1693_; 
v___x_1691_ = ((size_t)1ULL);
v___x_1692_ = lean_usize_add(v_i_1683_, v___x_1691_);
v___x_1693_ = lean_array_uset(v_bs_x27_1688_, v_i_1683_, v___y_1690_);
v_i_1683_ = v___x_1692_;
v_bs_1684_ = v___x_1693_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0___boxed(lean_object* v_f_1714_, lean_object* v_sz_1715_, lean_object* v_i_1716_, lean_object* v_bs_1717_){
_start:
{
size_t v_sz_boxed_1718_; size_t v_i_boxed_1719_; lean_object* v_res_1720_; 
v_sz_boxed_1718_ = lean_unbox_usize(v_sz_1715_);
lean_dec(v_sz_1715_);
v_i_boxed_1719_ = lean_unbox_usize(v_i_1716_);
lean_dec(v_i_1716_);
v_res_1720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(v_f_1714_, v_sz_boxed_1718_, v_i_boxed_1719_, v_bs_1717_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_mapVars(lean_object* v_f_1721_, lean_object* v_b_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_IR_MapVars_mapFnBody(v_f_1721_, v_b_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lam__0(lean_object* v_x_1724_, lean_object* v_y_1725_, lean_object* v_z_1726_){
_start:
{
uint8_t v___x_1727_; 
v___x_1727_ = l_Lean_IR_instBEqVarId_beq(v_x_1724_, v_z_1726_);
if (v___x_1727_ == 0)
{
lean_inc(v_z_1726_);
return v_z_1726_;
}
else
{
lean_inc(v_y_1725_);
return v_y_1725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lam__0___boxed(lean_object* v_x_1728_, lean_object* v_y_1729_, lean_object* v_z_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_IR_FnBody_replaceVar___lam__0(v_x_1728_, v_y_1729_, v_z_1730_);
lean_dec(v_z_1730_);
lean_dec(v_y_1729_);
lean_dec(v_x_1728_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar(lean_object* v_x_1732_, lean_object* v_y_1733_, lean_object* v_b_1734_){
_start:
{
lean_object* v___f_1735_; lean_object* v___x_1736_; 
v___f_1735_ = lean_alloc_closure((void*)(l_Lean_IR_FnBody_replaceVar___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1735_, 0, v_x_1732_);
lean_closure_set(v___f_1735_, 1, v_y_1733_);
v___x_1736_ = l_Lean_IR_MapVars_mapFnBody(v___f_1735_, v_b_1734_);
return v___x_1736_;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_NormIds(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_IR_Basic(builtin);
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
res = initialize_Lean_Compiler_IR_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_NormIds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_IR_NormIds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_IR_NormIds(builtin);
}
#ifdef __cplusplus
}
#endif
