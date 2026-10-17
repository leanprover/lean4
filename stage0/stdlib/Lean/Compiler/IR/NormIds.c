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
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_IR_instBEqVarId_beq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normFnBody___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normDecl___boxed(lean_object*, lean_object*, lean_object*);
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
v_k_32_ = lean_ctor_get(v_impl_28_, 1);
v_v_33_ = lean_ctor_get(v_impl_28_, 2);
v_l_34_ = lean_ctor_get(v_impl_28_, 3);
lean_inc(v_l_34_);
v_r_35_ = lean_ctor_get(v_impl_28_, 4);
v___x_36_ = lean_unsigned_to_nat(3u);
v___x_37_ = lean_nat_mul(v___x_36_, v_size_30_);
v___x_38_ = lean_nat_dec_lt(v___x_37_, v_size_31_);
lean_dec(v___x_37_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_42_; 
lean_dec(v_l_34_);
v___x_39_ = lean_nat_add(v___x_29_, v_size_30_);
v___x_40_ = lean_nat_add(v___x_39_, v_size_31_);
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
lean_inc(v_r_35_);
lean_inc(v_v_33_);
lean_inc(v_k_32_);
lean_inc(v_size_31_);
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
v_k_170_ = lean_ctor_get(v_impl_166_, 1);
v_v_171_ = lean_ctor_get(v_impl_166_, 2);
v_l_172_ = lean_ctor_get(v_impl_166_, 3);
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
v___x_177_ = lean_nat_add(v___x_167_, v_size_169_);
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
lean_inc(v_l_172_);
lean_inc(v_v_171_);
lean_inc(v_k_170_);
lean_inc(v_size_169_);
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
v___x_203_ = lean_nat_add(v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec(v___y_201_);
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
lean_ctor_set(v___x_183_, 3, v___y_200_);
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
lean_ctor_set(v_reuseFailAlloc_208_, 3, v___y_200_);
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
v___y_200_ = v___x_215_;
v___y_201_ = v___x_216_;
v___y_202_ = v_size_217_;
goto v___jp_199_;
}
else
{
lean_object* v___x_218_; 
v___x_218_ = lean_unsigned_to_nat(0u);
v___y_200_ = v___x_215_;
v___y_201_ = v___x_216_;
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
if (lean_obj_tag(v_l_253_) == 0)
{
lean_object* v_r_254_; lean_object* v_k_255_; lean_object* v_v_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_267_; 
lean_inc_ref(v_l_253_);
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
lean_inc(v_l_253_);
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
uint8_t v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_309_ = 1;
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
uint8_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec(v_id_306_);
v___x_314_ = 0;
v___x_315_ = lean_box(v___x_314_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v_a_307_);
return v___x_316_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0(lean_object* v_00_u03b2_317_, lean_object* v_k_318_, lean_object* v_t_319_){
_start:
{
uint8_t v___x_320_; 
v___x_320_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___redArg(v_k_318_, v_t_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0___boxed(lean_object* v_00_u03b2_321_, lean_object* v_k_322_, lean_object* v_t_323_){
_start:
{
uint8_t v_res_324_; lean_object* v_r_325_; 
v_res_324_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_UniqueIds_checkId_spec__0(v_00_u03b2_321_, v_k_322_, v_t_323_);
lean_dec(v_t_323_);
lean_dec(v_k_322_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1(lean_object* v_00_u03b2_326_, lean_object* v_k_327_, lean_object* v_v_328_, lean_object* v_t_329_, lean_object* v_hl_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_k_327_, v_v_328_, v_t_329_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0(lean_object* v_as_332_, size_t v_i_333_, size_t v_stop_334_, lean_object* v___y_335_){
_start:
{
uint8_t v___x_336_; 
v___x_336_ = lean_usize_dec_eq(v_i_333_, v_stop_334_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v_x_338_; lean_object* v___x_339_; lean_object* v_fst_340_; uint8_t v___x_341_; 
v___x_337_ = lean_array_uget_borrowed(v_as_332_, v_i_333_);
v_x_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_x_338_);
v___x_339_ = l_Lean_IR_UniqueIds_checkId(v_x_338_, v___y_335_);
v_fst_340_ = lean_ctor_get(v___x_339_, 0);
v___x_341_ = lean_unbox(v_fst_340_);
if (v___x_341_ == 0)
{
lean_object* v_snd_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_351_; 
v_snd_342_ = lean_ctor_get(v___x_339_, 1);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_351_ == 0)
{
lean_object* v_unused_352_; 
v_unused_352_ = lean_ctor_get(v___x_339_, 0);
lean_dec(v_unused_352_);
v___x_344_ = v___x_339_;
v_isShared_345_ = v_isSharedCheck_351_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_snd_342_);
lean_dec(v___x_339_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_351_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
uint8_t v___x_346_; lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_346_ = 1;
v___x_347_ = lean_box(v___x_346_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_347_);
v___x_349_ = v___x_344_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_snd_342_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
else
{
lean_object* v_snd_353_; size_t v___x_354_; size_t v___x_355_; 
v_snd_353_ = lean_ctor_get(v___x_339_, 1);
lean_inc(v_snd_353_);
lean_dec_ref(v___x_339_);
v___x_354_ = ((size_t)1ULL);
v___x_355_ = lean_usize_add(v_i_333_, v___x_354_);
v_i_333_ = v___x_355_;
v___y_335_ = v_snd_353_;
goto _start;
}
}
else
{
uint8_t v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = 0;
v___x_358_ = lean_box(v___x_357_);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v___y_335_);
return v___x_359_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0___boxed(lean_object* v_as_360_, lean_object* v_i_361_, lean_object* v_stop_362_, lean_object* v___y_363_){
_start:
{
size_t v_i_boxed_364_; size_t v_stop_boxed_365_; lean_object* v_res_366_; 
v_i_boxed_364_ = lean_unbox_usize(v_i_361_);
lean_dec(v_i_361_);
v_stop_boxed_365_ = lean_unbox_usize(v_stop_362_);
lean_dec(v_stop_362_);
v_res_366_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0(v_as_360_, v_i_boxed_364_, v_stop_boxed_365_, v___y_363_);
lean_dec_ref(v_as_360_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkParams(lean_object* v_ps_367_, lean_object* v_a_368_){
_start:
{
lean_object* v___y_370_; lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = lean_array_get_size(v_ps_367_);
v___x_376_ = lean_nat_dec_lt(v___x_374_, v___x_375_);
if (v___x_376_ == 0)
{
v___y_370_ = v_a_368_;
goto v___jp_369_;
}
else
{
if (v___x_376_ == 0)
{
v___y_370_ = v_a_368_;
goto v___jp_369_;
}
else
{
size_t v___x_377_; size_t v___x_378_; lean_object* v___x_379_; lean_object* v_fst_380_; uint8_t v___x_381_; 
v___x_377_ = ((size_t)0ULL);
v___x_378_ = lean_usize_of_nat(v___x_375_);
v___x_379_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0(v_ps_367_, v___x_377_, v___x_378_, v_a_368_);
v_fst_380_ = lean_ctor_get(v___x_379_, 0);
v___x_381_ = lean_unbox(v_fst_380_);
if (v___x_381_ == 0)
{
lean_object* v_snd_382_; 
v_snd_382_ = lean_ctor_get(v___x_379_, 1);
lean_inc(v_snd_382_);
lean_dec_ref(v___x_379_);
v___y_370_ = v_snd_382_;
goto v___jp_369_;
}
else
{
lean_object* v_snd_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_392_; 
v_snd_383_ = lean_ctor_get(v___x_379_, 1);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_392_ == 0)
{
lean_object* v_unused_393_; 
v_unused_393_ = lean_ctor_get(v___x_379_, 0);
lean_dec(v_unused_393_);
v___x_385_ = v___x_379_;
v_isShared_386_ = v_isSharedCheck_392_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_snd_383_);
lean_dec(v___x_379_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_392_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
uint8_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_387_ = 0;
v___x_388_ = lean_box(v___x_387_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v___x_388_);
v___x_390_ = v___x_385_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_snd_383_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
v___jp_369_:
{
uint8_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = 1;
v___x_372_ = lean_box(v___x_371_);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v___y_370_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkParams___boxed(lean_object* v_ps_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_IR_UniqueIds_checkParams(v_ps_394_, v_a_395_);
lean_dec_ref(v_ps_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkFnBody(lean_object* v_x_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___y_400_; 
switch(lean_obj_tag(v_x_397_))
{
case 0:
{
lean_object* v_x_404_; lean_object* v_b_405_; lean_object* v___x_406_; lean_object* v_fst_407_; uint8_t v___x_408_; 
v_x_404_ = lean_ctor_get(v_x_397_, 0);
lean_inc(v_x_404_);
v_b_405_ = lean_ctor_get(v_x_397_, 3);
lean_inc(v_b_405_);
lean_dec_ref_known(v_x_397_, 4);
v___x_406_ = l_Lean_IR_UniqueIds_checkId(v_x_404_, v_a_398_);
v_fst_407_ = lean_ctor_get(v___x_406_, 0);
v___x_408_ = lean_unbox(v_fst_407_);
if (v___x_408_ == 0)
{
lean_dec(v_b_405_);
return v___x_406_;
}
else
{
lean_object* v_snd_409_; 
v_snd_409_ = lean_ctor_get(v___x_406_, 1);
lean_inc(v_snd_409_);
lean_dec_ref(v___x_406_);
v_x_397_ = v_b_405_;
v_a_398_ = v_snd_409_;
goto _start;
}
}
case 1:
{
lean_object* v_j_411_; lean_object* v_xs_412_; lean_object* v_b_413_; lean_object* v___x_414_; lean_object* v_fst_415_; uint8_t v___x_416_; 
v_j_411_ = lean_ctor_get(v_x_397_, 0);
lean_inc(v_j_411_);
v_xs_412_ = lean_ctor_get(v_x_397_, 1);
lean_inc_ref(v_xs_412_);
v_b_413_ = lean_ctor_get(v_x_397_, 3);
lean_inc(v_b_413_);
lean_dec_ref_known(v_x_397_, 4);
v___x_414_ = l_Lean_IR_UniqueIds_checkId(v_j_411_, v_a_398_);
v_fst_415_ = lean_ctor_get(v___x_414_, 0);
v___x_416_ = lean_unbox(v_fst_415_);
if (v___x_416_ == 0)
{
lean_dec(v_b_413_);
lean_dec_ref(v_xs_412_);
return v___x_414_;
}
else
{
lean_object* v_snd_417_; lean_object* v___x_418_; lean_object* v_fst_419_; uint8_t v___x_420_; 
v_snd_417_ = lean_ctor_get(v___x_414_, 1);
lean_inc(v_snd_417_);
lean_dec_ref(v___x_414_);
v___x_418_ = l_Lean_IR_UniqueIds_checkParams(v_xs_412_, v_snd_417_);
lean_dec_ref(v_xs_412_);
v_fst_419_ = lean_ctor_get(v___x_418_, 0);
v___x_420_ = lean_unbox(v_fst_419_);
if (v___x_420_ == 0)
{
lean_dec(v_b_413_);
return v___x_418_;
}
else
{
lean_object* v_snd_421_; 
v_snd_421_ = lean_ctor_get(v___x_418_, 1);
lean_inc(v_snd_421_);
lean_dec_ref(v___x_418_);
v_x_397_ = v_b_413_;
v_a_398_ = v_snd_421_;
goto _start;
}
}
}
case 9:
{
lean_object* v_cs_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v_cs_423_ = lean_ctor_get(v_x_397_, 3);
lean_inc_ref(v_cs_423_);
lean_dec_ref_known(v_x_397_, 4);
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_array_get_size(v_cs_423_);
v___x_426_ = lean_nat_dec_lt(v___x_424_, v___x_425_);
if (v___x_426_ == 0)
{
lean_dec_ref(v_cs_423_);
v___y_400_ = v_a_398_;
goto v___jp_399_;
}
else
{
if (v___x_426_ == 0)
{
lean_dec_ref(v_cs_423_);
v___y_400_ = v_a_398_;
goto v___jp_399_;
}
else
{
size_t v___x_427_; size_t v___x_428_; lean_object* v___x_429_; lean_object* v_fst_430_; uint8_t v___x_431_; 
v___x_427_ = ((size_t)0ULL);
v___x_428_ = lean_usize_of_nat(v___x_425_);
v___x_429_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(v_cs_423_, v___x_427_, v___x_428_, v_a_398_);
lean_dec_ref(v_cs_423_);
v_fst_430_ = lean_ctor_get(v___x_429_, 0);
v___x_431_ = lean_unbox(v_fst_430_);
if (v___x_431_ == 0)
{
lean_object* v_snd_432_; 
v_snd_432_ = lean_ctor_get(v___x_429_, 1);
lean_inc(v_snd_432_);
lean_dec_ref(v___x_429_);
v___y_400_ = v_snd_432_;
goto v___jp_399_;
}
else
{
lean_object* v_snd_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_442_; 
v_snd_433_ = lean_ctor_get(v___x_429_, 1);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; 
v_unused_443_ = lean_ctor_get(v___x_429_, 0);
lean_dec(v_unused_443_);
v___x_435_ = v___x_429_;
v_isShared_436_ = v_isSharedCheck_442_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_snd_433_);
lean_dec(v___x_429_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_442_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
uint8_t v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_437_ = 0;
v___x_438_ = lean_box(v___x_437_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_438_);
v___x_440_ = v___x_435_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_snd_433_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
}
}
default: 
{
uint8_t v___x_444_; 
v___x_444_ = l_Lean_IR_FnBody_isTerminal(v_x_397_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_IR_FnBody_body(v_x_397_);
lean_dec(v_x_397_);
v_x_397_ = v___x_445_;
goto _start;
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec(v_x_397_);
v___x_447_ = lean_box(v___x_444_);
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v_a_398_);
return v___x_448_;
}
}
}
v___jp_399_:
{
uint8_t v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_401_ = 1;
v___x_402_ = lean_box(v___x_401_);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___y_400_);
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(lean_object* v_as_449_, size_t v_i_450_, size_t v_stop_451_, lean_object* v___y_452_){
_start:
{
uint8_t v___x_453_; 
v___x_453_ = lean_usize_dec_eq(v_i_450_, v_stop_451_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v_fst_457_; uint8_t v___x_458_; 
v___x_454_ = lean_array_uget_borrowed(v_as_449_, v_i_450_);
v___x_455_ = l_Lean_IR_Alt_body(v___x_454_);
v___x_456_ = l_Lean_IR_UniqueIds_checkFnBody(v___x_455_, v___y_452_);
v_fst_457_ = lean_ctor_get(v___x_456_, 0);
v___x_458_ = lean_unbox(v_fst_457_);
if (v___x_458_ == 0)
{
lean_object* v_snd_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_468_; 
v_snd_459_ = lean_ctor_get(v___x_456_, 1);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; 
v_unused_469_ = lean_ctor_get(v___x_456_, 0);
lean_dec(v_unused_469_);
v___x_461_ = v___x_456_;
v_isShared_462_ = v_isSharedCheck_468_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_snd_459_);
lean_dec(v___x_456_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_468_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_463_ = 1;
v___x_464_ = lean_box(v___x_463_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_464_);
v___x_466_ = v___x_461_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_snd_459_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
else
{
lean_object* v_snd_470_; size_t v___x_471_; size_t v___x_472_; 
v_snd_470_ = lean_ctor_get(v___x_456_, 1);
lean_inc(v_snd_470_);
lean_dec_ref(v___x_456_);
v___x_471_ = ((size_t)1ULL);
v___x_472_ = lean_usize_add(v_i_450_, v___x_471_);
v_i_450_ = v___x_472_;
v___y_452_ = v_snd_470_;
goto _start;
}
}
else
{
uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = 0;
v___x_475_ = lean_box(v___x_474_);
v___x_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
lean_ctor_set(v___x_476_, 1, v___y_452_);
return v___x_476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0___boxed(lean_object* v_as_477_, lean_object* v_i_478_, lean_object* v_stop_479_, lean_object* v___y_480_){
_start:
{
size_t v_i_boxed_481_; size_t v_stop_boxed_482_; lean_object* v_res_483_; 
v_i_boxed_481_ = lean_unbox_usize(v_i_478_);
lean_dec(v_i_478_);
v_stop_boxed_482_ = lean_unbox_usize(v_stop_479_);
lean_dec(v_stop_479_);
v_res_483_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(v_as_477_, v_i_boxed_481_, v_stop_boxed_482_, v___y_480_);
lean_dec_ref(v_as_477_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkDecl(lean_object* v_x_484_, lean_object* v_a_485_){
_start:
{
if (lean_obj_tag(v_x_484_) == 0)
{
lean_object* v_xs_486_; lean_object* v_body_487_; lean_object* v___x_488_; lean_object* v_fst_489_; uint8_t v___x_490_; 
v_xs_486_ = lean_ctor_get(v_x_484_, 1);
lean_inc_ref(v_xs_486_);
v_body_487_ = lean_ctor_get(v_x_484_, 3);
lean_inc(v_body_487_);
lean_dec_ref_known(v_x_484_, 5);
v___x_488_ = l_Lean_IR_UniqueIds_checkParams(v_xs_486_, v_a_485_);
lean_dec_ref(v_xs_486_);
v_fst_489_ = lean_ctor_get(v___x_488_, 0);
v___x_490_ = lean_unbox(v_fst_489_);
if (v___x_490_ == 0)
{
lean_dec(v_body_487_);
return v___x_488_;
}
else
{
lean_object* v_snd_491_; lean_object* v___x_492_; 
v_snd_491_ = lean_ctor_get(v___x_488_, 1);
lean_inc(v_snd_491_);
lean_dec_ref(v___x_488_);
v___x_492_ = l_Lean_IR_UniqueIds_checkFnBody(v_body_487_, v_snd_491_);
return v___x_492_;
}
}
else
{
lean_object* v_xs_493_; lean_object* v___x_494_; 
v_xs_493_ = lean_ctor_get(v_x_484_, 1);
lean_inc_ref(v_xs_493_);
lean_dec_ref_known(v_x_484_, 4);
v___x_494_ = l_Lean_IR_UniqueIds_checkParams(v_xs_493_, v_a_485_);
lean_dec_ref(v_xs_493_);
return v___x_494_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Decl_uniqueIds(lean_object* v_d_495_){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v_fst_498_; uint8_t v___x_499_; 
v___x_496_ = lean_box(1);
v___x_497_ = l_Lean_IR_UniqueIds_checkDecl(v_d_495_, v___x_496_);
v_fst_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_fst_498_);
lean_dec_ref(v___x_497_);
v___x_499_ = lean_unbox(v_fst_498_);
lean_dec(v_fst_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_uniqueIds___boxed(lean_object* v_d_500_){
_start:
{
uint8_t v_res_501_; lean_object* v_r_502_; 
v_res_501_ = l_Lean_IR_Decl_uniqueIds(v_d_500_);
v_r_502_ = lean_box(v_res_501_);
return v_r_502_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(lean_object* v_t_503_, lean_object* v_k_504_){
_start:
{
if (lean_obj_tag(v_t_503_) == 0)
{
lean_object* v_k_505_; lean_object* v_v_506_; lean_object* v_l_507_; lean_object* v_r_508_; uint8_t v___x_509_; 
v_k_505_ = lean_ctor_get(v_t_503_, 1);
v_v_506_ = lean_ctor_get(v_t_503_, 2);
v_l_507_ = lean_ctor_get(v_t_503_, 3);
v_r_508_ = lean_ctor_get(v_t_503_, 4);
v___x_509_ = lean_nat_dec_lt(v_k_504_, v_k_505_);
if (v___x_509_ == 0)
{
uint8_t v___x_510_; 
v___x_510_ = lean_nat_dec_eq(v_k_504_, v_k_505_);
if (v___x_510_ == 0)
{
v_t_503_ = v_r_508_;
goto _start;
}
else
{
lean_object* v___x_512_; 
lean_inc(v_v_506_);
v___x_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_512_, 0, v_v_506_);
return v___x_512_;
}
}
else
{
v_t_503_ = v_l_507_;
goto _start;
}
}
else
{
lean_object* v___x_514_; 
v___x_514_ = lean_box(0);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg___boxed(lean_object* v_t_515_, lean_object* v_k_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_t_515_, v_k_516_);
lean_dec(v_k_516_);
lean_dec(v_t_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normIndex(lean_object* v_x_518_, lean_object* v_m_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_m_519_, v_x_518_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_inc(v_x_518_);
return v_x_518_;
}
else
{
lean_object* v_val_521_; 
v_val_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_val_521_);
lean_dec_ref_known(v___x_520_, 1);
return v_val_521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normIndex___boxed(lean_object* v_x_522_, lean_object* v_m_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_IR_NormalizeIds_normIndex(v_x_522_, v_m_523_);
lean_dec(v_m_523_);
lean_dec(v_x_522_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0(lean_object* v_00_u03b4_525_, lean_object* v_t_526_, lean_object* v_k_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_t_526_, v_k_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___boxed(lean_object* v_00_u03b4_529_, lean_object* v_t_530_, lean_object* v_k_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0(v_00_u03b4_529_, v_t_530_, v_k_531_);
lean_dec(v_k_531_);
lean_dec(v_t_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normVar(lean_object* v_x_533_, lean_object* v_a_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_IR_NormalizeIds_normIndex(v_x_533_, v_a_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normVar___boxed(lean_object* v_x_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_IR_NormalizeIds_normVar(v_x_536_, v_a_537_);
lean_dec(v_a_537_);
lean_dec(v_x_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normJP(lean_object* v_x_539_, lean_object* v_a_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_IR_NormalizeIds_normIndex(v_x_539_, v_a_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normJP___boxed(lean_object* v_x_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_IR_NormalizeIds_normJP(v_x_542_, v_a_543_);
lean_dec(v_a_543_);
lean_dec(v_x_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArg(lean_object* v_x_545_, lean_object* v_a_546_){
_start:
{
if (lean_obj_tag(v_x_545_) == 0)
{
lean_object* v_id_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_555_; 
v_id_547_ = lean_ctor_get(v_x_545_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v_x_545_);
if (v_isSharedCheck_555_ == 0)
{
v___x_549_ = v_x_545_;
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_id_547_);
lean_dec(v_x_545_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = l_Lean_IR_NormalizeIds_normIndex(v_id_547_, v_a_546_);
lean_dec(v_id_547_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_551_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
else
{
return v_x_545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArg___boxed(lean_object* v_x_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_IR_NormalizeIds_normArg(v_x_556_, v_a_557_);
lean_dec(v_a_557_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(lean_object* v_m_559_, size_t v_sz_560_, size_t v_i_561_, lean_object* v_bs_562_){
_start:
{
uint8_t v___x_563_; 
v___x_563_ = lean_usize_dec_lt(v_i_561_, v_sz_560_);
if (v___x_563_ == 0)
{
return v_bs_562_;
}
else
{
lean_object* v_v_564_; lean_object* v___x_565_; lean_object* v_bs_x27_566_; lean_object* v___x_567_; size_t v___x_568_; size_t v___x_569_; lean_object* v___x_570_; 
v_v_564_ = lean_array_uget(v_bs_562_, v_i_561_);
v___x_565_ = lean_unsigned_to_nat(0u);
v_bs_x27_566_ = lean_array_uset(v_bs_562_, v_i_561_, v___x_565_);
v___x_567_ = l_Lean_IR_NormalizeIds_normArg(v_v_564_, v_m_559_);
v___x_568_ = ((size_t)1ULL);
v___x_569_ = lean_usize_add(v_i_561_, v___x_568_);
v___x_570_ = lean_array_uset(v_bs_x27_566_, v_i_561_, v___x_567_);
v_i_561_ = v___x_569_;
v_bs_562_ = v___x_570_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0___boxed(lean_object* v_m_572_, lean_object* v_sz_573_, lean_object* v_i_574_, lean_object* v_bs_575_){
_start:
{
size_t v_sz_boxed_576_; size_t v_i_boxed_577_; lean_object* v_res_578_; 
v_sz_boxed_576_ = lean_unbox_usize(v_sz_573_);
lean_dec(v_sz_573_);
v_i_boxed_577_ = lean_unbox_usize(v_i_574_);
lean_dec(v_i_574_);
v_res_578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(v_m_572_, v_sz_boxed_576_, v_i_boxed_577_, v_bs_575_);
lean_dec(v_m_572_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArgs(lean_object* v_as_579_, lean_object* v_m_580_){
_start:
{
size_t v_sz_581_; size_t v___x_582_; lean_object* v___x_583_; 
v_sz_581_ = lean_array_size(v_as_579_);
v___x_582_ = ((size_t)0ULL);
v___x_583_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(v_m_580_, v_sz_581_, v___x_582_, v_as_579_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArgs___boxed(lean_object* v_as_584_, lean_object* v_m_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_IR_NormalizeIds_normArgs(v_as_584_, v_m_585_);
lean_dec(v_m_585_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normExpr(lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
switch(lean_obj_tag(v_x_587_))
{
case 0:
{
lean_object* v_i_589_; lean_object* v_ys_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_598_; 
v_i_589_ = lean_ctor_get(v_x_587_, 0);
v_ys_590_ = lean_ctor_get(v_x_587_, 1);
v_isSharedCheck_598_ = !lean_is_exclusive(v_x_587_);
if (v_isSharedCheck_598_ == 0)
{
v___x_592_ = v_x_587_;
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_ys_590_);
lean_inc(v_i_589_);
lean_dec(v_x_587_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_594_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_590_, v_x_588_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v___x_594_);
v___x_596_ = v___x_592_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_i_589_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___x_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
case 1:
{
lean_object* v_n_599_; lean_object* v_x_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_608_; 
v_n_599_ = lean_ctor_get(v_x_587_, 0);
v_x_600_ = lean_ctor_get(v_x_587_, 1);
v_isSharedCheck_608_ = !lean_is_exclusive(v_x_587_);
if (v_isSharedCheck_608_ == 0)
{
v___x_602_ = v_x_587_;
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_x_600_);
lean_inc(v_n_599_);
lean_dec(v_x_587_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = l_Lean_IR_NormalizeIds_normIndex(v_x_600_, v_x_588_);
lean_dec(v_x_600_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 1, v___x_604_);
v___x_606_ = v___x_602_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_n_599_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v___x_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
case 2:
{
lean_object* v_x_609_; lean_object* v_i_610_; uint8_t v_updtHeader_611_; lean_object* v_ys_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_621_; 
v_x_609_ = lean_ctor_get(v_x_587_, 0);
v_i_610_ = lean_ctor_get(v_x_587_, 1);
v_updtHeader_611_ = lean_ctor_get_uint8(v_x_587_, sizeof(void*)*3);
v_ys_612_ = lean_ctor_get(v_x_587_, 2);
v_isSharedCheck_621_ = !lean_is_exclusive(v_x_587_);
if (v_isSharedCheck_621_ == 0)
{
v___x_614_ = v_x_587_;
v_isShared_615_ = v_isSharedCheck_621_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_ys_612_);
lean_inc(v_i_610_);
lean_inc(v_x_609_);
lean_dec(v_x_587_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_621_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_616_ = l_Lean_IR_NormalizeIds_normIndex(v_x_609_, v_x_588_);
lean_dec(v_x_609_);
v___x_617_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_612_, v_x_588_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 2, v___x_617_);
lean_ctor_set(v___x_614_, 0, v___x_616_);
v___x_619_ = v___x_614_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_i_610_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v___x_617_);
lean_ctor_set_uint8(v_reuseFailAlloc_620_, sizeof(void*)*3, v_updtHeader_611_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
case 3:
{
lean_object* v_i_622_; lean_object* v_x_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_631_; 
v_i_622_ = lean_ctor_get(v_x_587_, 0);
v_x_623_ = lean_ctor_get(v_x_587_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_x_587_);
if (v_isSharedCheck_631_ == 0)
{
v___x_625_ = v_x_587_;
v_isShared_626_ = v_isSharedCheck_631_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_x_623_);
lean_inc(v_i_622_);
lean_dec(v_x_587_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_631_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_627_ = l_Lean_IR_NormalizeIds_normIndex(v_x_623_, v_x_588_);
lean_dec(v_x_623_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___x_627_);
v___x_629_ = v___x_625_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_i_622_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
case 4:
{
lean_object* v_i_632_; lean_object* v_x_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_641_; 
v_i_632_ = lean_ctor_get(v_x_587_, 0);
v_x_633_ = lean_ctor_get(v_x_587_, 1);
v_isSharedCheck_641_ = !lean_is_exclusive(v_x_587_);
if (v_isSharedCheck_641_ == 0)
{
v___x_635_ = v_x_587_;
v_isShared_636_ = v_isSharedCheck_641_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_x_633_);
lean_inc(v_i_632_);
lean_dec(v_x_587_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_641_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_637_ = l_Lean_IR_NormalizeIds_normIndex(v_x_633_, v_x_588_);
lean_dec(v_x_633_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 1, v___x_637_);
v___x_639_ = v___x_635_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_i_632_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
case 5:
{
lean_object* v_n_642_; lean_object* v_offset_643_; lean_object* v_x_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_652_; 
v_n_642_ = lean_ctor_get(v_x_587_, 0);
v_offset_643_ = lean_ctor_get(v_x_587_, 1);
v_x_644_ = lean_ctor_get(v_x_587_, 2);
v_isSharedCheck_652_ = !lean_is_exclusive(v_x_587_);
if (v_isSharedCheck_652_ == 0)
{
v___x_646_ = v_x_587_;
v_isShared_647_ = v_isSharedCheck_652_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_x_644_);
lean_inc(v_offset_643_);
lean_inc(v_n_642_);
lean_dec(v_x_587_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_652_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_648_ = l_Lean_IR_NormalizeIds_normIndex(v_x_644_, v_x_588_);
lean_dec(v_x_644_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 2, v___x_648_);
v___x_650_ = v___x_646_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_n_642_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_offset_643_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
case 6:
{
lean_object* v_c_653_; lean_object* v_ys_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_662_; 
v_c_653_ = lean_ctor_get(v_x_587_, 0);
v_ys_654_ = lean_ctor_get(v_x_587_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v_x_587_);
if (v_isSharedCheck_662_ == 0)
{
v___x_656_ = v_x_587_;
v_isShared_657_ = v_isSharedCheck_662_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_ys_654_);
lean_inc(v_c_653_);
lean_dec(v_x_587_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_662_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_658_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_654_, v_x_588_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 1, v___x_658_);
v___x_660_ = v___x_656_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_c_653_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v___x_658_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
case 7:
{
lean_object* v_c_663_; lean_object* v_ys_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_672_; 
v_c_663_ = lean_ctor_get(v_x_587_, 0);
v_ys_664_ = lean_ctor_get(v_x_587_, 1);
v_isSharedCheck_672_ = !lean_is_exclusive(v_x_587_);
if (v_isSharedCheck_672_ == 0)
{
v___x_666_ = v_x_587_;
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_ys_664_);
lean_inc(v_c_663_);
lean_dec(v_x_587_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_668_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_664_, v_x_588_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v___x_668_);
v___x_670_ = v___x_666_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_c_663_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
case 8:
{
lean_object* v_x_673_; lean_object* v_ys_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_683_; 
v_x_673_ = lean_ctor_get(v_x_587_, 0);
v_ys_674_ = lean_ctor_get(v_x_587_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v_x_587_);
if (v_isSharedCheck_683_ == 0)
{
v___x_676_ = v_x_587_;
v_isShared_677_ = v_isSharedCheck_683_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_ys_674_);
lean_inc(v_x_673_);
lean_dec(v_x_587_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_683_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_678_ = l_Lean_IR_NormalizeIds_normIndex(v_x_673_, v_x_588_);
lean_dec(v_x_673_);
v___x_679_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_674_, v_x_588_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 1, v___x_679_);
lean_ctor_set(v___x_676_, 0, v___x_678_);
v___x_681_ = v___x_676_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
case 9:
{
lean_object* v_ty_684_; lean_object* v_x_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_693_; 
v_ty_684_ = lean_ctor_get(v_x_587_, 0);
v_x_685_ = lean_ctor_get(v_x_587_, 1);
v_isSharedCheck_693_ = !lean_is_exclusive(v_x_587_);
if (v_isSharedCheck_693_ == 0)
{
v___x_687_ = v_x_587_;
v_isShared_688_ = v_isSharedCheck_693_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_x_685_);
lean_inc(v_ty_684_);
lean_dec(v_x_587_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_693_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = l_Lean_IR_NormalizeIds_normIndex(v_x_685_, v_x_588_);
lean_dec(v_x_685_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_689_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_ty_684_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
case 10:
{
lean_object* v_x_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_702_; 
v_x_694_ = lean_ctor_get(v_x_587_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v_x_587_);
if (v_isSharedCheck_702_ == 0)
{
v___x_696_ = v_x_587_;
v_isShared_697_ = v_isSharedCheck_702_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_x_694_);
lean_dec(v_x_587_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_702_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_698_ = l_Lean_IR_NormalizeIds_normIndex(v_x_694_, v_x_588_);
lean_dec(v_x_694_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_698_);
v___x_700_ = v___x_696_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
case 11:
{
return v_x_587_;
}
default: 
{
lean_object* v_x_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_711_; 
v_x_703_ = lean_ctor_get(v_x_587_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v_x_587_);
if (v_isSharedCheck_711_ == 0)
{
v___x_705_ = v_x_587_;
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_x_703_);
lean_dec(v_x_587_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_707_ = l_Lean_IR_NormalizeIds_normIndex(v_x_703_, v_x_588_);
lean_dec(v_x_703_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_707_);
v___x_709_ = v___x_705_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
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
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normExpr___boxed(lean_object* v_x_712_, lean_object* v_x_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_IR_NormalizeIds_normExpr(v_x_712_, v_x_713_);
lean_dec(v_x_713_);
return v_res_714_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_NormalizeIds_withVar___redArg___lam__0(lean_object* v_x_715_, lean_object* v_y_716_){
_start:
{
uint8_t v___x_717_; 
v___x_717_ = lean_nat_dec_lt(v_x_715_, v_y_716_);
if (v___x_717_ == 0)
{
uint8_t v___x_718_; 
v___x_718_ = lean_nat_dec_eq(v_x_715_, v_y_716_);
if (v___x_718_ == 0)
{
uint8_t v___x_719_; 
v___x_719_ = 2;
return v___x_719_;
}
else
{
uint8_t v___x_720_; 
v___x_720_ = 1;
return v___x_720_;
}
}
else
{
uint8_t v___x_721_; 
v___x_721_ = 0;
return v___x_721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg___lam__0___boxed(lean_object* v_x_722_, lean_object* v_y_723_){
_start:
{
uint8_t v_res_724_; lean_object* v_r_725_; 
v_res_724_ = l_Lean_IR_NormalizeIds_withVar___redArg___lam__0(v_x_722_, v_y_723_);
lean_dec(v_y_723_);
lean_dec(v_x_722_);
v_r_725_ = lean_box(v_res_724_);
return v_r_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg(lean_object* v_x_727_, lean_object* v_k_728_, lean_object* v_m_729_, lean_object* v_a_730_){
_start:
{
lean_object* v___f_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___f_731_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_732_ = lean_unsigned_to_nat(1u);
v___x_733_ = lean_nat_add(v_a_730_, v___x_732_);
lean_inc(v_m_729_);
lean_inc(v_a_730_);
v___x_734_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_731_, v_x_727_, v_a_730_, v_m_729_);
v___x_735_ = lean_apply_3(v_k_728_, v_a_730_, v___x_734_, v___x_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg___boxed(lean_object* v_x_736_, lean_object* v_k_737_, lean_object* v_m_738_, lean_object* v_a_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_IR_NormalizeIds_withVar___redArg(v_x_736_, v_k_737_, v_m_738_, v_a_739_);
lean_dec(v_m_738_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar(lean_object* v_00_u03b1_741_, lean_object* v_x_742_, lean_object* v_k_743_, lean_object* v_m_744_, lean_object* v_a_745_){
_start:
{
lean_object* v___f_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___f_746_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_747_ = lean_unsigned_to_nat(1u);
v___x_748_ = lean_nat_add(v_a_745_, v___x_747_);
lean_inc(v_m_744_);
lean_inc(v_a_745_);
v___x_749_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_746_, v_x_742_, v_a_745_, v_m_744_);
v___x_750_ = lean_apply_3(v_k_743_, v_a_745_, v___x_749_, v___x_748_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___boxed(lean_object* v_00_u03b1_751_, lean_object* v_x_752_, lean_object* v_k_753_, lean_object* v_m_754_, lean_object* v_a_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_IR_NormalizeIds_withVar(v_00_u03b1_751_, v_x_752_, v_k_753_, v_m_754_, v_a_755_);
lean_dec(v_m_754_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___redArg(lean_object* v_x_757_, lean_object* v_k_758_, lean_object* v_m_759_, lean_object* v_a_760_){
_start:
{
lean_object* v___f_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___f_761_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = lean_nat_add(v_a_760_, v___x_762_);
lean_inc(v_m_759_);
lean_inc(v_a_760_);
v___x_764_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_761_, v_x_757_, v_a_760_, v_m_759_);
v___x_765_ = lean_apply_3(v_k_758_, v_a_760_, v___x_764_, v___x_763_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___redArg___boxed(lean_object* v_x_766_, lean_object* v_k_767_, lean_object* v_m_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_IR_NormalizeIds_withJP___redArg(v_x_766_, v_k_767_, v_m_768_, v_a_769_);
lean_dec(v_m_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP(lean_object* v_00_u03b1_771_, lean_object* v_x_772_, lean_object* v_k_773_, lean_object* v_m_774_, lean_object* v_a_775_){
_start:
{
lean_object* v___f_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___f_776_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_777_ = lean_unsigned_to_nat(1u);
v___x_778_ = lean_nat_add(v_a_775_, v___x_777_);
lean_inc(v_m_774_);
lean_inc(v_a_775_);
v___x_779_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_776_, v_x_772_, v_a_775_, v_m_774_);
v___x_780_ = lean_apply_3(v_k_773_, v_a_775_, v___x_779_, v___x_778_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___boxed(lean_object* v_00_u03b1_781_, lean_object* v_x_782_, lean_object* v_k_783_, lean_object* v_m_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_IR_NormalizeIds_withJP(v_00_u03b1_781_, v_x_782_, v_k_783_, v_m_784_, v_a_785_);
lean_dec(v_m_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__0(lean_object* v_fst_787_, lean_object* v_x_788_){
_start:
{
lean_object* v_x_789_; uint8_t v_borrow_790_; lean_object* v_ty_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_799_; 
v_x_789_ = lean_ctor_get(v_x_788_, 0);
v_borrow_790_ = lean_ctor_get_uint8(v_x_788_, sizeof(void*)*2);
v_ty_791_ = lean_ctor_get(v_x_788_, 1);
v_isSharedCheck_799_ = !lean_is_exclusive(v_x_788_);
if (v_isSharedCheck_799_ == 0)
{
v___x_793_ = v_x_788_;
v_isShared_794_ = v_isSharedCheck_799_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_ty_791_);
lean_inc(v_x_789_);
lean_dec(v_x_788_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_799_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_795_ = l_Lean_IR_NormalizeIds_normIndex(v_x_789_, v_fst_787_);
lean_dec(v_x_789_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_795_);
v___x_797_ = v___x_793_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_ty_791_);
lean_ctor_set_uint8(v_reuseFailAlloc_798_, sizeof(void*)*2, v_borrow_790_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed(lean_object* v_fst_800_, lean_object* v_x_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_IR_NormalizeIds_withParams___redArg___lam__0(v_fst_800_, v_x_801_);
lean_dec(v_fst_800_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__2(lean_object* v___f_803_, lean_object* v_m_804_, lean_object* v_p_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v_x_807_ = lean_ctor_get(v_p_805_, 0);
lean_inc(v_x_807_);
lean_dec_ref(v_p_805_);
v___x_808_ = lean_unsigned_to_nat(1u);
v___x_809_ = lean_nat_add(v___y_806_, v___x_808_);
v___x_810_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_803_, v_x_807_, v___y_806_, v_m_804_);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v___x_809_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg(lean_object* v_ps_859_, lean_object* v_k_860_, lean_object* v_m_861_, lean_object* v_a_862_){
_start:
{
lean_object* v___x_863_; lean_object* v_fst_865_; lean_object* v_snd_866_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_863_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__9));
v___x_872_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__19));
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = lean_array_get_size(v_ps_859_);
v___x_875_ = lean_nat_dec_lt(v___x_873_, v___x_874_);
if (v___x_875_ == 0)
{
lean_inc(v_m_861_);
v_fst_865_ = v_m_861_;
v_snd_866_ = v_a_862_;
goto v___jp_864_;
}
else
{
lean_object* v___f_876_; size_t v___x_877_; size_t v___x_878_; lean_object* v___x_787__overap_879_; lean_object* v___x_880_; lean_object* v_fst_881_; lean_object* v_snd_882_; 
v___f_876_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__20));
v___x_877_ = ((size_t)0ULL);
v___x_878_ = lean_usize_of_nat(v___x_874_);
lean_inc(v_m_861_);
lean_inc_ref(v_ps_859_);
v___x_787__overap_879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_872_, v___f_876_, v_ps_859_, v___x_877_, v___x_878_, v_m_861_);
v___x_880_ = lean_apply_1(v___x_787__overap_879_, v_a_862_);
v_fst_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_fst_881_);
v_snd_882_ = lean_ctor_get(v___x_880_, 1);
lean_inc(v_snd_882_);
lean_dec_ref(v___x_880_);
v_fst_865_ = v_fst_881_;
v_snd_866_ = v_snd_882_;
goto v___jp_864_;
}
v___jp_864_:
{
lean_object* v___f_867_; size_t v_sz_868_; size_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
lean_inc(v_fst_865_);
v___f_867_ = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_867_, 0, v_fst_865_);
v_sz_868_ = lean_array_size(v_ps_859_);
v___x_869_ = ((size_t)0ULL);
v___x_870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_863_, v___f_867_, v_sz_868_, v___x_869_, v_ps_859_);
v___x_871_ = lean_apply_3(v_k_860_, v___x_870_, v_fst_865_, v_snd_866_);
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___boxed(lean_object* v_ps_883_, lean_object* v_k_884_, lean_object* v_m_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_IR_NormalizeIds_withParams___redArg(v_ps_883_, v_k_884_, v_m_885_, v_a_886_);
lean_dec(v_m_885_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams(lean_object* v_00_u03b1_888_, lean_object* v_ps_889_, lean_object* v_k_890_, lean_object* v_m_891_, lean_object* v_a_892_){
_start:
{
lean_object* v___x_893_; lean_object* v_fst_895_; lean_object* v_snd_896_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_893_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__9));
v___x_902_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__19));
v___x_903_ = lean_unsigned_to_nat(0u);
v___x_904_ = lean_array_get_size(v_ps_889_);
v___x_905_ = lean_nat_dec_lt(v___x_903_, v___x_904_);
if (v___x_905_ == 0)
{
lean_inc(v_m_891_);
v_fst_895_ = v_m_891_;
v_snd_896_ = v_a_892_;
goto v___jp_894_;
}
else
{
lean_object* v___f_906_; size_t v___x_907_; size_t v___x_908_; lean_object* v___x_969__overap_909_; lean_object* v___x_910_; lean_object* v_fst_911_; lean_object* v_snd_912_; 
v___f_906_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__20));
v___x_907_ = ((size_t)0ULL);
v___x_908_ = lean_usize_of_nat(v___x_904_);
lean_inc(v_m_891_);
lean_inc_ref(v_ps_889_);
v___x_969__overap_909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_902_, v___f_906_, v_ps_889_, v___x_907_, v___x_908_, v_m_891_);
v___x_910_ = lean_apply_1(v___x_969__overap_909_, v_a_892_);
v_fst_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_fst_911_);
v_snd_912_ = lean_ctor_get(v___x_910_, 1);
lean_inc(v_snd_912_);
lean_dec_ref(v___x_910_);
v_fst_895_ = v_fst_911_;
v_snd_896_ = v_snd_912_;
goto v___jp_894_;
}
v___jp_894_:
{
lean_object* v___f_897_; size_t v_sz_898_; size_t v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
lean_inc(v_fst_895_);
v___f_897_ = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_897_, 0, v_fst_895_);
v_sz_898_ = lean_array_size(v_ps_889_);
v___x_899_ = ((size_t)0ULL);
v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_893_, v___f_897_, v_sz_898_, v___x_899_, v_ps_889_);
v___x_901_ = lean_apply_3(v_k_890_, v___x_900_, v_fst_895_, v_snd_896_);
return v___x_901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___boxed(lean_object* v_00_u03b1_913_, lean_object* v_ps_914_, lean_object* v_k_915_, lean_object* v_m_916_, lean_object* v_a_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_IR_NormalizeIds_withParams(v_00_u03b1_913_, v_ps_914_, v_k_915_, v_m_916_, v_a_917_);
lean_dec(v_m_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_instMonadLiftMN___lam__0(lean_object* v_00_u03b1_919_, lean_object* v_x_920_, lean_object* v_m_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_apply_1(v_x_920_, v_m_921_);
v___x_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set(v___x_924_, 1, v___y_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(lean_object* v_fst_927_, size_t v_sz_928_, size_t v_i_929_, lean_object* v_bs_930_){
_start:
{
uint8_t v___x_931_; 
v___x_931_ = lean_usize_dec_lt(v_i_929_, v_sz_928_);
if (v___x_931_ == 0)
{
return v_bs_930_;
}
else
{
lean_object* v_v_932_; lean_object* v_x_933_; uint8_t v_borrow_934_; lean_object* v_ty_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_949_; 
v_v_932_ = lean_array_uget(v_bs_930_, v_i_929_);
v_x_933_ = lean_ctor_get(v_v_932_, 0);
v_borrow_934_ = lean_ctor_get_uint8(v_v_932_, sizeof(void*)*2);
v_ty_935_ = lean_ctor_get(v_v_932_, 1);
v_isSharedCheck_949_ = !lean_is_exclusive(v_v_932_);
if (v_isSharedCheck_949_ == 0)
{
v___x_937_ = v_v_932_;
v_isShared_938_ = v_isSharedCheck_949_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_ty_935_);
lean_inc(v_x_933_);
lean_dec(v_v_932_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_949_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; lean_object* v_bs_x27_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_939_ = lean_unsigned_to_nat(0u);
v_bs_x27_940_ = lean_array_uset(v_bs_930_, v_i_929_, v___x_939_);
v___x_941_ = l_Lean_IR_NormalizeIds_normIndex(v_x_933_, v_fst_927_);
lean_dec(v_x_933_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_941_);
v___x_943_ = v___x_937_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_ty_935_);
lean_ctor_set_uint8(v_reuseFailAlloc_948_, sizeof(void*)*2, v_borrow_934_);
v___x_943_ = v_reuseFailAlloc_948_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
size_t v___x_944_; size_t v___x_945_; lean_object* v___x_946_; 
v___x_944_ = ((size_t)1ULL);
v___x_945_ = lean_usize_add(v_i_929_, v___x_944_);
v___x_946_ = lean_array_uset(v_bs_x27_940_, v_i_929_, v___x_943_);
v_i_929_ = v___x_945_;
v_bs_930_ = v___x_946_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0___boxed(lean_object* v_fst_950_, lean_object* v_sz_951_, lean_object* v_i_952_, lean_object* v_bs_953_){
_start:
{
size_t v_sz_boxed_954_; size_t v_i_boxed_955_; lean_object* v_res_956_; 
v_sz_boxed_954_ = lean_unbox_usize(v_sz_951_);
lean_dec(v_sz_951_);
v_i_boxed_955_ = lean_unbox_usize(v_i_952_);
lean_dec(v_i_952_);
v_res_956_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(v_fst_950_, v_sz_boxed_954_, v_i_boxed_955_, v_bs_953_);
lean_dec(v_fst_950_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(lean_object* v_as_957_, size_t v_i_958_, size_t v_stop_959_, lean_object* v_b_960_, lean_object* v___y_961_){
_start:
{
uint8_t v___x_962_; 
v___x_962_ = lean_usize_dec_eq(v_i_958_, v_stop_959_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v_x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; size_t v___x_968_; size_t v___x_969_; 
v___x_963_ = lean_array_uget_borrowed(v_as_957_, v_i_958_);
v_x_964_ = lean_ctor_get(v___x_963_, 0);
v___x_965_ = lean_unsigned_to_nat(1u);
v___x_966_ = lean_nat_add(v___y_961_, v___x_965_);
lean_inc(v_x_964_);
v___x_967_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_x_964_, v___y_961_, v_b_960_);
v___x_968_ = ((size_t)1ULL);
v___x_969_ = lean_usize_add(v_i_958_, v___x_968_);
v_i_958_ = v___x_969_;
v_b_960_ = v___x_967_;
v___y_961_ = v___x_966_;
goto _start;
}
else
{
lean_object* v___x_971_; 
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v_b_960_);
lean_ctor_set(v___x_971_, 1, v___y_961_);
return v___x_971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1___boxed(lean_object* v_as_972_, lean_object* v_i_973_, lean_object* v_stop_974_, lean_object* v_b_975_, lean_object* v___y_976_){
_start:
{
size_t v_i_boxed_977_; size_t v_stop_boxed_978_; lean_object* v_res_979_; 
v_i_boxed_977_ = lean_unbox_usize(v_i_973_);
lean_dec(v_i_973_);
v_stop_boxed_978_ = lean_unbox_usize(v_stop_974_);
lean_dec(v_stop_974_);
v_res_979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_as_972_, v_i_boxed_977_, v_stop_boxed_978_, v_b_975_, v___y_976_);
lean_dec_ref(v_as_972_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normFnBody(lean_object* v_x_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
switch(lean_obj_tag(v_x_980_))
{
case 0:
{
lean_object* v_x_983_; lean_object* v_ty_984_; lean_object* v_e_985_; lean_object* v_b_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1007_; 
v_x_983_ = lean_ctor_get(v_x_980_, 0);
v_ty_984_ = lean_ctor_get(v_x_980_, 1);
v_e_985_ = lean_ctor_get(v_x_980_, 2);
v_b_986_ = lean_ctor_get(v_x_980_, 3);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_x_980_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_988_ = v_x_980_;
v_isShared_989_ = v_isSharedCheck_1007_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_b_986_);
lean_inc(v_e_985_);
lean_inc(v_ty_984_);
lean_inc(v_x_983_);
lean_dec(v_x_980_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1007_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v_fst_994_; lean_object* v_snd_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1006_; 
v___x_990_ = lean_unsigned_to_nat(1u);
v___x_991_ = lean_nat_add(v_a_982_, v___x_990_);
lean_inc(v_a_981_);
lean_inc(v_a_982_);
v___x_992_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_x_983_, v_a_982_, v_a_981_);
v___x_993_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_986_, v___x_992_, v___x_991_);
lean_dec(v___x_992_);
v_fst_994_ = lean_ctor_get(v___x_993_, 0);
v_snd_995_ = lean_ctor_get(v___x_993_, 1);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_997_ = v___x_993_;
v_isShared_998_ = v_isSharedCheck_1006_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_snd_995_);
lean_inc(v_fst_994_);
lean_dec(v___x_993_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1006_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_999_ = l_Lean_IR_NormalizeIds_normExpr(v_e_985_, v_a_981_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 3, v_fst_994_);
lean_ctor_set(v___x_988_, 2, v___x_999_);
lean_ctor_set(v___x_988_, 0, v_a_982_);
v___x_1001_ = v___x_988_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_982_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_ty_984_);
lean_ctor_set(v_reuseFailAlloc_1005_, 2, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1005_, 3, v_fst_994_);
v___x_1001_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1003_; 
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_1001_);
v___x_1003_ = v___x_997_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_snd_995_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
}
case 1:
{
lean_object* v_j_1008_; lean_object* v_xs_1009_; lean_object* v_v_1010_; lean_object* v_b_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1048_; 
v_j_1008_ = lean_ctor_get(v_x_980_, 0);
v_xs_1009_ = lean_ctor_get(v_x_980_, 1);
v_v_1010_ = lean_ctor_get(v_x_980_, 2);
v_b_1011_ = lean_ctor_get(v_x_980_, 3);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_x_980_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1013_ = v_x_980_;
v_isShared_1014_ = v_isSharedCheck_1048_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_b_1011_);
lean_inc(v_v_1010_);
lean_inc(v_xs_1009_);
lean_inc(v_j_1008_);
lean_dec(v_x_980_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1048_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v_fst_1016_; lean_object* v_snd_1017_; lean_object* v___x_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v___x_1040_ = lean_unsigned_to_nat(0u);
v___x_1041_ = lean_array_get_size(v_xs_1009_);
v___x_1042_ = lean_nat_dec_lt(v___x_1040_, v___x_1041_);
if (v___x_1042_ == 0)
{
lean_inc(v_a_981_);
v_fst_1016_ = v_a_981_;
v_snd_1017_ = v_a_982_;
goto v___jp_1015_;
}
else
{
size_t v___x_1043_; size_t v___x_1044_; lean_object* v___x_1045_; lean_object* v_fst_1046_; lean_object* v_snd_1047_; 
v___x_1043_ = ((size_t)0ULL);
v___x_1044_ = lean_usize_of_nat(v___x_1041_);
lean_inc(v_a_981_);
v___x_1045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_1009_, v___x_1043_, v___x_1044_, v_a_981_, v_a_982_);
v_fst_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_fst_1046_);
v_snd_1047_ = lean_ctor_get(v___x_1045_, 1);
lean_inc(v_snd_1047_);
lean_dec_ref(v___x_1045_);
v_fst_1016_ = v_fst_1046_;
v_snd_1017_ = v_snd_1047_;
goto v___jp_1015_;
}
v___jp_1015_:
{
lean_object* v___x_1018_; lean_object* v_fst_1019_; lean_object* v_snd_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v_fst_1025_; lean_object* v_snd_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1039_; 
v___x_1018_ = l_Lean_IR_NormalizeIds_normFnBody(v_v_1010_, v_fst_1016_, v_snd_1017_);
v_fst_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_fst_1019_);
v_snd_1020_ = lean_ctor_get(v___x_1018_, 1);
lean_inc_n(v_snd_1020_, 2);
lean_dec_ref(v___x_1018_);
v___x_1021_ = lean_unsigned_to_nat(1u);
v___x_1022_ = lean_nat_add(v_snd_1020_, v___x_1021_);
lean_inc(v_a_981_);
v___x_1023_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_j_1008_, v_snd_1020_, v_a_981_);
v___x_1024_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1011_, v___x_1023_, v___x_1022_);
lean_dec(v___x_1023_);
v_fst_1025_ = lean_ctor_get(v___x_1024_, 0);
v_snd_1026_ = lean_ctor_get(v___x_1024_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1028_ = v___x_1024_;
v_isShared_1029_ = v_isSharedCheck_1039_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_snd_1026_);
lean_inc(v_fst_1025_);
lean_dec(v___x_1024_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1039_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
size_t v_sz_1030_; size_t v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v_sz_1030_ = lean_array_size(v_xs_1009_);
v___x_1031_ = ((size_t)0ULL);
v___x_1032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(v_fst_1016_, v_sz_1030_, v___x_1031_, v_xs_1009_);
lean_dec(v_fst_1016_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 3, v_fst_1025_);
lean_ctor_set(v___x_1013_, 2, v_fst_1019_);
lean_ctor_set(v___x_1013_, 1, v___x_1032_);
lean_ctor_set(v___x_1013_, 0, v_snd_1020_);
v___x_1034_ = v___x_1013_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_snd_1020_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1038_, 2, v_fst_1019_);
lean_ctor_set(v_reuseFailAlloc_1038_, 3, v_fst_1025_);
v___x_1034_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1036_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1034_);
v___x_1036_ = v___x_1028_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_snd_1026_);
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
}
case 2:
{
lean_object* v_x_1049_; lean_object* v_i_1050_; lean_object* v_y_1051_; lean_object* v_b_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1071_; 
v_x_1049_ = lean_ctor_get(v_x_980_, 0);
v_i_1050_ = lean_ctor_get(v_x_980_, 1);
v_y_1051_ = lean_ctor_get(v_x_980_, 2);
v_b_1052_ = lean_ctor_get(v_x_980_, 3);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_x_980_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1054_ = v_x_980_;
v_isShared_1055_ = v_isSharedCheck_1071_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_b_1052_);
lean_inc(v_y_1051_);
lean_inc(v_i_1050_);
lean_inc(v_x_1049_);
lean_dec(v_x_980_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1071_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v_fst_1059_; lean_object* v_snd_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1070_; 
v___x_1056_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1049_, v_a_981_);
lean_dec(v_x_1049_);
v___x_1057_ = l_Lean_IR_NormalizeIds_normArg(v_y_1051_, v_a_981_);
v___x_1058_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1052_, v_a_981_, v_a_982_);
v_fst_1059_ = lean_ctor_get(v___x_1058_, 0);
v_snd_1060_ = lean_ctor_get(v___x_1058_, 1);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1062_ = v___x_1058_;
v_isShared_1063_ = v_isSharedCheck_1070_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_snd_1060_);
lean_inc(v_fst_1059_);
lean_dec(v___x_1058_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1070_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 3, v_fst_1059_);
lean_ctor_set(v___x_1054_, 2, v___x_1057_);
lean_ctor_set(v___x_1054_, 0, v___x_1056_);
v___x_1065_ = v___x_1054_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_i_1050_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1069_, 3, v_fst_1059_);
v___x_1065_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1067_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v___x_1065_);
v___x_1067_ = v___x_1062_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_snd_1060_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
case 3:
{
lean_object* v_x_1072_; lean_object* v_cidx_1073_; lean_object* v_b_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1092_; 
v_x_1072_ = lean_ctor_get(v_x_980_, 0);
v_cidx_1073_ = lean_ctor_get(v_x_980_, 1);
v_b_1074_ = lean_ctor_get(v_x_980_, 2);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_x_980_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1076_ = v_x_980_;
v_isShared_1077_ = v_isSharedCheck_1092_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_b_1074_);
lean_inc(v_cidx_1073_);
lean_inc(v_x_1072_);
lean_dec(v_x_980_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1092_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v_fst_1080_; lean_object* v_snd_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1091_; 
v___x_1078_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1072_, v_a_981_);
lean_dec(v_x_1072_);
v___x_1079_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1074_, v_a_981_, v_a_982_);
v_fst_1080_ = lean_ctor_get(v___x_1079_, 0);
v_snd_1081_ = lean_ctor_get(v___x_1079_, 1);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1083_ = v___x_1079_;
v_isShared_1084_ = v_isSharedCheck_1091_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_snd_1081_);
lean_inc(v_fst_1080_);
lean_dec(v___x_1079_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1091_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 2, v_fst_1080_);
lean_ctor_set(v___x_1076_, 0, v___x_1078_);
v___x_1086_ = v___x_1076_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_cidx_1073_);
lean_ctor_set(v_reuseFailAlloc_1090_, 2, v_fst_1080_);
v___x_1086_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1088_; 
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1086_);
v___x_1088_ = v___x_1083_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_snd_1081_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
case 4:
{
lean_object* v_x_1093_; lean_object* v_i_1094_; lean_object* v_y_1095_; lean_object* v_b_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1115_; 
v_x_1093_ = lean_ctor_get(v_x_980_, 0);
v_i_1094_ = lean_ctor_get(v_x_980_, 1);
v_y_1095_ = lean_ctor_get(v_x_980_, 2);
v_b_1096_ = lean_ctor_get(v_x_980_, 3);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_x_980_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1098_ = v_x_980_;
v_isShared_1099_ = v_isSharedCheck_1115_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_b_1096_);
lean_inc(v_y_1095_);
lean_inc(v_i_1094_);
lean_inc(v_x_1093_);
lean_dec(v_x_980_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1115_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v_fst_1103_; lean_object* v_snd_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1114_; 
v___x_1100_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1093_, v_a_981_);
lean_dec(v_x_1093_);
v___x_1101_ = l_Lean_IR_NormalizeIds_normIndex(v_y_1095_, v_a_981_);
lean_dec(v_y_1095_);
v___x_1102_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1096_, v_a_981_, v_a_982_);
v_fst_1103_ = lean_ctor_get(v___x_1102_, 0);
v_snd_1104_ = lean_ctor_get(v___x_1102_, 1);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1106_ = v___x_1102_;
v_isShared_1107_ = v_isSharedCheck_1114_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_snd_1104_);
lean_inc(v_fst_1103_);
lean_dec(v___x_1102_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1114_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 3, v_fst_1103_);
lean_ctor_set(v___x_1098_, 2, v___x_1101_);
lean_ctor_set(v___x_1098_, 0, v___x_1100_);
v___x_1109_ = v___x_1098_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_i_1094_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v_fst_1103_);
v___x_1109_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1111_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1109_);
v___x_1111_ = v___x_1106_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_snd_1104_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
case 5:
{
lean_object* v_x_1116_; lean_object* v_i_1117_; lean_object* v_offset_1118_; lean_object* v_y_1119_; lean_object* v_ty_1120_; lean_object* v_b_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1140_; 
v_x_1116_ = lean_ctor_get(v_x_980_, 0);
v_i_1117_ = lean_ctor_get(v_x_980_, 1);
v_offset_1118_ = lean_ctor_get(v_x_980_, 2);
v_y_1119_ = lean_ctor_get(v_x_980_, 3);
v_ty_1120_ = lean_ctor_get(v_x_980_, 4);
v_b_1121_ = lean_ctor_get(v_x_980_, 5);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_x_980_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1123_ = v_x_980_;
v_isShared_1124_ = v_isSharedCheck_1140_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_b_1121_);
lean_inc(v_ty_1120_);
lean_inc(v_y_1119_);
lean_inc(v_offset_1118_);
lean_inc(v_i_1117_);
lean_inc(v_x_1116_);
lean_dec(v_x_980_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1140_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v_fst_1128_; lean_object* v_snd_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1139_; 
v___x_1125_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1116_, v_a_981_);
lean_dec(v_x_1116_);
v___x_1126_ = l_Lean_IR_NormalizeIds_normIndex(v_y_1119_, v_a_981_);
lean_dec(v_y_1119_);
v___x_1127_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1121_, v_a_981_, v_a_982_);
v_fst_1128_ = lean_ctor_get(v___x_1127_, 0);
v_snd_1129_ = lean_ctor_get(v___x_1127_, 1);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1131_ = v___x_1127_;
v_isShared_1132_ = v_isSharedCheck_1139_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_snd_1129_);
lean_inc(v_fst_1128_);
lean_dec(v___x_1127_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1139_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 5, v_fst_1128_);
lean_ctor_set(v___x_1123_, 3, v___x_1126_);
lean_ctor_set(v___x_1123_, 0, v___x_1125_);
v___x_1134_ = v___x_1123_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1125_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_i_1117_);
lean_ctor_set(v_reuseFailAlloc_1138_, 2, v_offset_1118_);
lean_ctor_set(v_reuseFailAlloc_1138_, 3, v___x_1126_);
lean_ctor_set(v_reuseFailAlloc_1138_, 4, v_ty_1120_);
lean_ctor_set(v_reuseFailAlloc_1138_, 5, v_fst_1128_);
v___x_1134_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1136_; 
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1134_);
v___x_1136_ = v___x_1131_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_snd_1129_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
case 6:
{
lean_object* v_x_1141_; lean_object* v_n_1142_; uint8_t v_c_1143_; uint8_t v_persistent_1144_; lean_object* v_b_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1163_; 
v_x_1141_ = lean_ctor_get(v_x_980_, 0);
v_n_1142_ = lean_ctor_get(v_x_980_, 1);
v_c_1143_ = lean_ctor_get_uint8(v_x_980_, sizeof(void*)*3);
v_persistent_1144_ = lean_ctor_get_uint8(v_x_980_, sizeof(void*)*3 + 1);
v_b_1145_ = lean_ctor_get(v_x_980_, 2);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_x_980_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1147_ = v_x_980_;
v_isShared_1148_ = v_isSharedCheck_1163_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_b_1145_);
lean_inc(v_n_1142_);
lean_inc(v_x_1141_);
lean_dec(v_x_980_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1163_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v_fst_1151_; lean_object* v_snd_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1162_; 
v___x_1149_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1141_, v_a_981_);
lean_dec(v_x_1141_);
v___x_1150_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1145_, v_a_981_, v_a_982_);
v_fst_1151_ = lean_ctor_get(v___x_1150_, 0);
v_snd_1152_ = lean_ctor_get(v___x_1150_, 1);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1154_ = v___x_1150_;
v_isShared_1155_ = v_isSharedCheck_1162_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_snd_1152_);
lean_inc(v_fst_1151_);
lean_dec(v___x_1150_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1162_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 2, v_fst_1151_);
lean_ctor_set(v___x_1147_, 0, v___x_1149_);
v___x_1157_ = v___x_1147_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_n_1142_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_fst_1151_);
lean_ctor_set_uint8(v_reuseFailAlloc_1161_, sizeof(void*)*3, v_c_1143_);
lean_ctor_set_uint8(v_reuseFailAlloc_1161_, sizeof(void*)*3 + 1, v_persistent_1144_);
v___x_1157_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1159_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1157_);
v___x_1159_ = v___x_1154_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_snd_1152_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
case 7:
{
lean_object* v_x_1164_; lean_object* v_n_1165_; uint8_t v_c_1166_; uint8_t v_persistent_1167_; lean_object* v_b_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1186_; 
v_x_1164_ = lean_ctor_get(v_x_980_, 0);
v_n_1165_ = lean_ctor_get(v_x_980_, 1);
v_c_1166_ = lean_ctor_get_uint8(v_x_980_, sizeof(void*)*3);
v_persistent_1167_ = lean_ctor_get_uint8(v_x_980_, sizeof(void*)*3 + 1);
v_b_1168_ = lean_ctor_get(v_x_980_, 2);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_x_980_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1170_ = v_x_980_;
v_isShared_1171_ = v_isSharedCheck_1186_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_b_1168_);
lean_inc(v_n_1165_);
lean_inc(v_x_1164_);
lean_dec(v_x_980_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1186_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v_fst_1174_; lean_object* v_snd_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1185_; 
v___x_1172_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1164_, v_a_981_);
lean_dec(v_x_1164_);
v___x_1173_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1168_, v_a_981_, v_a_982_);
v_fst_1174_ = lean_ctor_get(v___x_1173_, 0);
v_snd_1175_ = lean_ctor_get(v___x_1173_, 1);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1177_ = v___x_1173_;
v_isShared_1178_ = v_isSharedCheck_1185_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_snd_1175_);
lean_inc(v_fst_1174_);
lean_dec(v___x_1173_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1185_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 2, v_fst_1174_);
lean_ctor_set(v___x_1170_, 0, v___x_1172_);
v___x_1180_ = v___x_1170_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1172_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_n_1165_);
lean_ctor_set(v_reuseFailAlloc_1184_, 2, v_fst_1174_);
lean_ctor_set_uint8(v_reuseFailAlloc_1184_, sizeof(void*)*3, v_c_1166_);
lean_ctor_set_uint8(v_reuseFailAlloc_1184_, sizeof(void*)*3 + 1, v_persistent_1167_);
v___x_1180_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1182_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1180_);
v___x_1182_ = v___x_1177_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_snd_1175_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
case 8:
{
lean_object* v_x_1187_; lean_object* v_b_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1206_; 
v_x_1187_ = lean_ctor_get(v_x_980_, 0);
v_b_1188_ = lean_ctor_get(v_x_980_, 1);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_x_980_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1190_ = v_x_980_;
v_isShared_1191_ = v_isSharedCheck_1206_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_b_1188_);
lean_inc(v_x_1187_);
lean_dec(v_x_980_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1206_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v_fst_1194_; lean_object* v_snd_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1205_; 
v___x_1192_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1187_, v_a_981_);
lean_dec(v_x_1187_);
v___x_1193_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1188_, v_a_981_, v_a_982_);
v_fst_1194_ = lean_ctor_get(v___x_1193_, 0);
v_snd_1195_ = lean_ctor_get(v___x_1193_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1197_ = v___x_1193_;
v_isShared_1198_ = v_isSharedCheck_1205_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_snd_1195_);
lean_inc(v_fst_1194_);
lean_dec(v___x_1193_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1205_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 1, v_fst_1194_);
lean_ctor_set(v___x_1190_, 0, v___x_1192_);
v___x_1200_ = v___x_1190_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_fst_1194_);
v___x_1200_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1202_; 
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1200_);
v___x_1202_ = v___x_1197_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_snd_1195_);
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
}
case 9:
{
lean_object* v_tid_1207_; lean_object* v_x_1208_; lean_object* v_xType_1209_; lean_object* v_cs_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1230_; 
v_tid_1207_ = lean_ctor_get(v_x_980_, 0);
v_x_1208_ = lean_ctor_get(v_x_980_, 1);
v_xType_1209_ = lean_ctor_get(v_x_980_, 2);
v_cs_1210_ = lean_ctor_get(v_x_980_, 3);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_x_980_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1212_ = v_x_980_;
v_isShared_1213_ = v_isSharedCheck_1230_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_cs_1210_);
lean_inc(v_xType_1209_);
lean_inc(v_x_1208_);
lean_inc(v_tid_1207_);
lean_dec(v_x_980_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1230_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; size_t v_sz_1215_; size_t v___x_1216_; lean_object* v___x_1217_; lean_object* v_fst_1218_; lean_object* v_snd_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1229_; 
v___x_1214_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1208_, v_a_981_);
lean_dec(v_x_1208_);
v_sz_1215_ = lean_array_size(v_cs_1210_);
v___x_1216_ = ((size_t)0ULL);
v___x_1217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(v_sz_1215_, v___x_1216_, v_cs_1210_, v_a_981_, v_a_982_);
v_fst_1218_ = lean_ctor_get(v___x_1217_, 0);
v_snd_1219_ = lean_ctor_get(v___x_1217_, 1);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1221_ = v___x_1217_;
v_isShared_1222_ = v_isSharedCheck_1229_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_snd_1219_);
lean_inc(v_fst_1218_);
lean_dec(v___x_1217_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1229_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 3, v_fst_1218_);
lean_ctor_set(v___x_1212_, 1, v___x_1214_);
v___x_1224_ = v___x_1212_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_tid_1207_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_xType_1209_);
lean_ctor_set(v_reuseFailAlloc_1228_, 3, v_fst_1218_);
v___x_1224_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1226_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1224_);
v___x_1226_ = v___x_1221_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_snd_1219_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
case 10:
{
lean_object* v_x_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1240_; 
v_x_1231_ = lean_ctor_get(v_x_980_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_x_980_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1233_ = v_x_980_;
v_isShared_1234_ = v_isSharedCheck_1240_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_x_1231_);
lean_dec(v_x_980_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1240_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1235_ = l_Lean_IR_NormalizeIds_normArg(v_x_1231_, v_a_981_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1235_);
v___x_1237_ = v___x_1233_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; 
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
lean_ctor_set(v___x_1238_, 1, v_a_982_);
return v___x_1238_;
}
}
}
case 11:
{
lean_object* v_j_1241_; lean_object* v_ys_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1252_; 
v_j_1241_ = lean_ctor_get(v_x_980_, 0);
v_ys_1242_ = lean_ctor_get(v_x_980_, 1);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_x_980_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1244_ = v_x_980_;
v_isShared_1245_ = v_isSharedCheck_1252_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_ys_1242_);
lean_inc(v_j_1241_);
lean_dec(v_x_980_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1252_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1246_ = l_Lean_IR_NormalizeIds_normIndex(v_j_1241_, v_a_981_);
lean_dec(v_j_1241_);
v___x_1247_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_1242_, v_a_981_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v___x_1247_);
lean_ctor_set(v___x_1244_, 0, v___x_1246_);
v___x_1249_ = v___x_1244_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v_a_982_);
return v___x_1250_;
}
}
}
default: 
{
lean_object* v___x_1253_; 
v___x_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1253_, 0, v_x_980_);
lean_ctor_set(v___x_1253_, 1, v_a_982_);
return v___x_1253_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(size_t v_sz_1254_, size_t v_i_1255_, lean_object* v_bs_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
uint8_t v___x_1259_; 
v___x_1259_ = lean_usize_dec_lt(v_i_1255_, v_sz_1254_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v_bs_1256_);
lean_ctor_set(v___x_1260_, 1, v___y_1258_);
return v___x_1260_;
}
else
{
lean_object* v_v_1261_; lean_object* v___x_1262_; lean_object* v_bs_x27_1263_; lean_object* v_fst_1265_; lean_object* v_snd_1266_; 
v_v_1261_ = lean_array_uget(v_bs_1256_, v_i_1255_);
v___x_1262_ = lean_unsigned_to_nat(0u);
v_bs_x27_1263_ = lean_array_uset(v_bs_1256_, v_i_1255_, v___x_1262_);
if (lean_obj_tag(v_v_1261_) == 0)
{
lean_object* v_info_1271_; lean_object* v_b_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1282_; 
v_info_1271_ = lean_ctor_get(v_v_1261_, 0);
v_b_1272_ = lean_ctor_get(v_v_1261_, 1);
v_isSharedCheck_1282_ = !lean_is_exclusive(v_v_1261_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1274_ = v_v_1261_;
v_isShared_1275_ = v_isSharedCheck_1282_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_b_1272_);
lean_inc(v_info_1271_);
lean_dec(v_v_1261_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1282_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v_fst_1277_; lean_object* v_snd_1278_; lean_object* v___x_1280_; 
v___x_1276_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1272_, v___y_1257_, v___y_1258_);
v_fst_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_fst_1277_);
v_snd_1278_ = lean_ctor_get(v___x_1276_, 1);
lean_inc(v_snd_1278_);
lean_dec_ref(v___x_1276_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 1, v_fst_1277_);
v___x_1280_ = v___x_1274_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_info_1271_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_fst_1277_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
v_fst_1265_ = v___x_1280_;
v_snd_1266_ = v_snd_1278_;
goto v___jp_1264_;
}
}
}
else
{
lean_object* v_b_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1293_; 
v_b_1283_ = lean_ctor_get(v_v_1261_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_v_1261_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1285_ = v_v_1261_;
v_isShared_1286_ = v_isSharedCheck_1293_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_b_1283_);
lean_dec(v_v_1261_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1293_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v_fst_1288_; lean_object* v_snd_1289_; lean_object* v___x_1291_; 
v___x_1287_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1283_, v___y_1257_, v___y_1258_);
v_fst_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_fst_1288_);
v_snd_1289_ = lean_ctor_get(v___x_1287_, 1);
lean_inc(v_snd_1289_);
lean_dec_ref(v___x_1287_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v_fst_1288_);
v___x_1291_ = v___x_1285_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_fst_1288_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
v_fst_1265_ = v___x_1291_;
v_snd_1266_ = v_snd_1289_;
goto v___jp_1264_;
}
}
}
v___jp_1264_:
{
size_t v___x_1267_; size_t v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = ((size_t)1ULL);
v___x_1268_ = lean_usize_add(v_i_1255_, v___x_1267_);
v___x_1269_ = lean_array_uset(v_bs_x27_1263_, v_i_1255_, v_fst_1265_);
v_i_1255_ = v___x_1268_;
v_bs_1256_ = v___x_1269_;
v___y_1258_ = v_snd_1266_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2___boxed(lean_object* v_sz_1294_, lean_object* v_i_1295_, lean_object* v_bs_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
size_t v_sz_boxed_1299_; size_t v_i_boxed_1300_; lean_object* v_res_1301_; 
v_sz_boxed_1299_ = lean_unbox_usize(v_sz_1294_);
lean_dec(v_sz_1294_);
v_i_boxed_1300_ = lean_unbox_usize(v_i_1295_);
lean_dec(v_i_1295_);
v_res_1301_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(v_sz_boxed_1299_, v_i_boxed_1300_, v_bs_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1297_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normFnBody___boxed(lean_object* v_x_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_IR_NormalizeIds_normFnBody(v_x_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_a_1303_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normDecl(lean_object* v_d_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
if (lean_obj_tag(v_d_1306_) == 0)
{
lean_object* v_xs_1309_; lean_object* v_body_1310_; lean_object* v_fst_1312_; lean_object* v_snd_1313_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v_xs_1309_ = lean_ctor_get(v_d_1306_, 1);
v_body_1310_ = lean_ctor_get(v_d_1306_, 3);
v___x_1325_ = lean_unsigned_to_nat(0u);
v___x_1326_ = lean_array_get_size(v_xs_1309_);
v___x_1327_ = lean_nat_dec_lt(v___x_1325_, v___x_1326_);
if (v___x_1327_ == 0)
{
lean_inc(v_a_1307_);
v_fst_1312_ = v_a_1307_;
v_snd_1313_ = v_a_1308_;
goto v___jp_1311_;
}
else
{
size_t v___x_1328_; size_t v___x_1329_; lean_object* v___x_1330_; lean_object* v_fst_1331_; lean_object* v_snd_1332_; 
v___x_1328_ = ((size_t)0ULL);
v___x_1329_ = lean_usize_of_nat(v___x_1326_);
lean_inc(v_a_1307_);
v___x_1330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_1309_, v___x_1328_, v___x_1329_, v_a_1307_, v_a_1308_);
v_fst_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_fst_1331_);
v_snd_1332_ = lean_ctor_get(v___x_1330_, 1);
lean_inc(v_snd_1332_);
lean_dec_ref(v___x_1330_);
v_fst_1312_ = v_fst_1331_;
v_snd_1313_ = v_snd_1332_;
goto v___jp_1311_;
}
v___jp_1311_:
{
lean_object* v___x_1314_; lean_object* v_fst_1315_; lean_object* v_snd_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1324_; 
lean_inc(v_body_1310_);
v___x_1314_ = l_Lean_IR_NormalizeIds_normFnBody(v_body_1310_, v_fst_1312_, v_snd_1313_);
lean_dec(v_fst_1312_);
v_fst_1315_ = lean_ctor_get(v___x_1314_, 0);
v_snd_1316_ = lean_ctor_get(v___x_1314_, 1);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1318_ = v___x_1314_;
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_snd_1316_);
lean_inc(v_fst_1315_);
lean_dec(v___x_1314_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = l_Lean_IR_Decl_updateBody_x21(v_d_1306_, v_fst_1315_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1320_);
v___x_1322_ = v___x_1318_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_snd_1316_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
else
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1333_, 0, v_d_1306_);
lean_ctor_set(v___x_1333_, 1, v_a_1308_);
return v___x_1333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normDecl___boxed(lean_object* v_d_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_IR_NormalizeIds_normDecl(v_d_1334_, v_a_1335_, v_a_1336_);
lean_dec(v_a_1335_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_normalizeIds(lean_object* v_d_1338_){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v_fst_1342_; 
v___x_1339_ = lean_box(1);
v___x_1340_ = lean_unsigned_to_nat(1u);
v___x_1341_ = l_Lean_IR_NormalizeIds_normDecl(v_d_1338_, v___x_1339_, v___x_1340_);
v_fst_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_fst_1342_);
lean_dec_ref(v___x_1341_);
return v_fst_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArg(lean_object* v_f_1343_, lean_object* v_x_1344_){
_start:
{
if (lean_obj_tag(v_x_1344_) == 0)
{
lean_object* v_id_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1353_; 
v_id_1345_ = lean_ctor_get(v_x_1344_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_x_1344_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1347_ = v_x_1344_;
v_isShared_1348_ = v_isSharedCheck_1353_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_id_1345_);
lean_dec(v_x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1353_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1349_ = lean_apply_1(v_f_1343_, v_id_1345_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1349_);
v___x_1351_ = v___x_1347_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
else
{
lean_dec_ref(v_f_1343_);
return v_x_1344_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(lean_object* v_f_1354_, size_t v_sz_1355_, size_t v_i_1356_, lean_object* v_bs_1357_){
_start:
{
uint8_t v___x_1358_; 
v___x_1358_ = lean_usize_dec_lt(v_i_1356_, v_sz_1355_);
if (v___x_1358_ == 0)
{
lean_dec_ref(v_f_1354_);
return v_bs_1357_;
}
else
{
lean_object* v_v_1359_; lean_object* v___x_1360_; lean_object* v_bs_x27_1361_; lean_object* v___y_1363_; 
v_v_1359_ = lean_array_uget(v_bs_1357_, v_i_1356_);
v___x_1360_ = lean_unsigned_to_nat(0u);
v_bs_x27_1361_ = lean_array_uset(v_bs_1357_, v_i_1356_, v___x_1360_);
if (lean_obj_tag(v_v_1359_) == 0)
{
lean_object* v_id_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1376_; 
v_id_1368_ = lean_ctor_get(v_v_1359_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_v_1359_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1370_ = v_v_1359_;
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_id_1368_);
lean_dec(v_v_1359_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
lean_inc_ref(v_f_1354_);
v___x_1372_ = lean_apply_1(v_f_1354_, v_id_1368_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1372_);
v___x_1374_ = v___x_1370_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
v___y_1363_ = v___x_1374_;
goto v___jp_1362_;
}
}
}
else
{
v___y_1363_ = v_v_1359_;
goto v___jp_1362_;
}
v___jp_1362_:
{
size_t v___x_1364_; size_t v___x_1365_; lean_object* v___x_1366_; 
v___x_1364_ = ((size_t)1ULL);
v___x_1365_ = lean_usize_add(v_i_1356_, v___x_1364_);
v___x_1366_ = lean_array_uset(v_bs_x27_1361_, v_i_1356_, v___y_1363_);
v_i_1356_ = v___x_1365_;
v_bs_1357_ = v___x_1366_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0___boxed(lean_object* v_f_1377_, lean_object* v_sz_1378_, lean_object* v_i_1379_, lean_object* v_bs_1380_){
_start:
{
size_t v_sz_boxed_1381_; size_t v_i_boxed_1382_; lean_object* v_res_1383_; 
v_sz_boxed_1381_ = lean_unbox_usize(v_sz_1378_);
lean_dec(v_sz_1378_);
v_i_boxed_1382_ = lean_unbox_usize(v_i_1379_);
lean_dec(v_i_1379_);
v_res_1383_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(v_f_1377_, v_sz_boxed_1381_, v_i_boxed_1382_, v_bs_1380_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArgs(lean_object* v_f_1384_, lean_object* v_as_1385_){
_start:
{
size_t v_sz_1386_; size_t v___x_1387_; lean_object* v___x_1388_; 
v_sz_1386_ = lean_array_size(v_as_1385_);
v___x_1387_ = ((size_t)0ULL);
v___x_1388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(v_f_1384_, v_sz_1386_, v___x_1387_, v_as_1385_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapExpr(lean_object* v_f_1389_, lean_object* v_x_1390_){
_start:
{
switch(lean_obj_tag(v_x_1390_))
{
case 0:
{
lean_object* v_i_1391_; lean_object* v_ys_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1400_; 
v_i_1391_ = lean_ctor_get(v_x_1390_, 0);
v_ys_1392_ = lean_ctor_get(v_x_1390_, 1);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_x_1390_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1394_ = v_x_1390_;
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_ys_1392_);
lean_inc(v_i_1391_);
lean_dec(v_x_1390_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1396_ = l_Lean_IR_MapVars_mapArgs(v_f_1389_, v_ys_1392_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 1, v___x_1396_);
v___x_1398_ = v___x_1394_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_i_1391_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
case 1:
{
lean_object* v_n_1401_; lean_object* v_x_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1410_; 
v_n_1401_ = lean_ctor_get(v_x_1390_, 0);
v_x_1402_ = lean_ctor_get(v_x_1390_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_x_1390_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1404_ = v_x_1390_;
v_isShared_1405_ = v_isSharedCheck_1410_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_x_1402_);
lean_inc(v_n_1401_);
lean_dec(v_x_1390_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1410_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1406_ = lean_apply_1(v_f_1389_, v_x_1402_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 1, v___x_1406_);
v___x_1408_ = v___x_1404_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_n_1401_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
case 2:
{
lean_object* v_x_1411_; lean_object* v_i_1412_; uint8_t v_updtHeader_1413_; lean_object* v_ys_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1423_; 
v_x_1411_ = lean_ctor_get(v_x_1390_, 0);
v_i_1412_ = lean_ctor_get(v_x_1390_, 1);
v_updtHeader_1413_ = lean_ctor_get_uint8(v_x_1390_, sizeof(void*)*3);
v_ys_1414_ = lean_ctor_get(v_x_1390_, 2);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_x_1390_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1416_ = v_x_1390_;
v_isShared_1417_ = v_isSharedCheck_1423_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_ys_1414_);
lean_inc(v_i_1412_);
lean_inc(v_x_1411_);
lean_dec(v_x_1390_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1423_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
lean_inc_ref(v_f_1389_);
v___x_1418_ = lean_apply_1(v_f_1389_, v_x_1411_);
v___x_1419_ = l_Lean_IR_MapVars_mapArgs(v_f_1389_, v_ys_1414_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 2, v___x_1419_);
lean_ctor_set(v___x_1416_, 0, v___x_1418_);
v___x_1421_ = v___x_1416_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_i_1412_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v___x_1419_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*3, v_updtHeader_1413_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
case 3:
{
lean_object* v_i_1424_; lean_object* v_x_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1433_; 
v_i_1424_ = lean_ctor_get(v_x_1390_, 0);
v_x_1425_ = lean_ctor_get(v_x_1390_, 1);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_x_1390_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1427_ = v_x_1390_;
v_isShared_1428_ = v_isSharedCheck_1433_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_x_1425_);
lean_inc(v_i_1424_);
lean_dec(v_x_1390_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1433_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
v___x_1429_ = lean_apply_1(v_f_1389_, v_x_1425_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 1, v___x_1429_);
v___x_1431_ = v___x_1427_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_i_1424_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
case 4:
{
lean_object* v_i_1434_; lean_object* v_x_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1443_; 
v_i_1434_ = lean_ctor_get(v_x_1390_, 0);
v_x_1435_ = lean_ctor_get(v_x_1390_, 1);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_x_1390_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1437_ = v_x_1390_;
v_isShared_1438_ = v_isSharedCheck_1443_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_x_1435_);
lean_inc(v_i_1434_);
lean_dec(v_x_1390_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1443_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1439_ = lean_apply_1(v_f_1389_, v_x_1435_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 1, v___x_1439_);
v___x_1441_ = v___x_1437_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_i_1434_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
case 5:
{
lean_object* v_n_1444_; lean_object* v_offset_1445_; lean_object* v_x_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1454_; 
v_n_1444_ = lean_ctor_get(v_x_1390_, 0);
v_offset_1445_ = lean_ctor_get(v_x_1390_, 1);
v_x_1446_ = lean_ctor_get(v_x_1390_, 2);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_x_1390_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1448_ = v_x_1390_;
v_isShared_1449_ = v_isSharedCheck_1454_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_x_1446_);
lean_inc(v_offset_1445_);
lean_inc(v_n_1444_);
lean_dec(v_x_1390_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1454_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1450_ = lean_apply_1(v_f_1389_, v_x_1446_);
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 2, v___x_1450_);
v___x_1452_ = v___x_1448_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_n_1444_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_offset_1445_);
lean_ctor_set(v_reuseFailAlloc_1453_, 2, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
case 6:
{
lean_object* v_c_1455_; lean_object* v_ys_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1464_; 
v_c_1455_ = lean_ctor_get(v_x_1390_, 0);
v_ys_1456_ = lean_ctor_get(v_x_1390_, 1);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_x_1390_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1458_ = v_x_1390_;
v_isShared_1459_ = v_isSharedCheck_1464_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_ys_1456_);
lean_inc(v_c_1455_);
lean_dec(v_x_1390_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1464_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1460_ = l_Lean_IR_MapVars_mapArgs(v_f_1389_, v_ys_1456_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 1, v___x_1460_);
v___x_1462_ = v___x_1458_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_c_1455_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
case 7:
{
lean_object* v_c_1465_; lean_object* v_ys_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1474_; 
v_c_1465_ = lean_ctor_get(v_x_1390_, 0);
v_ys_1466_ = lean_ctor_get(v_x_1390_, 1);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_x_1390_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1468_ = v_x_1390_;
v_isShared_1469_ = v_isSharedCheck_1474_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_ys_1466_);
lean_inc(v_c_1465_);
lean_dec(v_x_1390_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1474_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1470_ = l_Lean_IR_MapVars_mapArgs(v_f_1389_, v_ys_1466_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 1, v___x_1470_);
v___x_1472_ = v___x_1468_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_c_1465_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
case 8:
{
lean_object* v_x_1475_; lean_object* v_ys_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1485_; 
v_x_1475_ = lean_ctor_get(v_x_1390_, 0);
v_ys_1476_ = lean_ctor_get(v_x_1390_, 1);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_x_1390_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1478_ = v_x_1390_;
v_isShared_1479_ = v_isSharedCheck_1485_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_ys_1476_);
lean_inc(v_x_1475_);
lean_dec(v_x_1390_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1485_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1483_; 
lean_inc_ref(v_f_1389_);
v___x_1480_ = lean_apply_1(v_f_1389_, v_x_1475_);
v___x_1481_ = l_Lean_IR_MapVars_mapArgs(v_f_1389_, v_ys_1476_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 1, v___x_1481_);
lean_ctor_set(v___x_1478_, 0, v___x_1480_);
v___x_1483_ = v___x_1478_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
case 9:
{
lean_object* v_ty_1486_; lean_object* v_x_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1495_; 
v_ty_1486_ = lean_ctor_get(v_x_1390_, 0);
v_x_1487_ = lean_ctor_get(v_x_1390_, 1);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_x_1390_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1489_ = v_x_1390_;
v_isShared_1490_ = v_isSharedCheck_1495_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_x_1487_);
lean_inc(v_ty_1486_);
lean_dec(v_x_1390_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1495_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1491_ = lean_apply_1(v_f_1389_, v_x_1487_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v___x_1491_);
v___x_1493_ = v___x_1489_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_ty_1486_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
case 10:
{
lean_object* v_x_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1504_; 
v_x_1496_ = lean_ctor_get(v_x_1390_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_x_1390_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1498_ = v_x_1390_;
v_isShared_1499_ = v_isSharedCheck_1504_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_x_1496_);
lean_dec(v_x_1390_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1504_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1500_ = lean_apply_1(v_f_1389_, v_x_1496_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 0, v___x_1500_);
v___x_1502_ = v___x_1498_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(10, 1, 0);
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
case 11:
{
lean_dec_ref(v_f_1389_);
return v_x_1390_;
}
default: 
{
lean_object* v_x_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1513_; 
v_x_1505_ = lean_ctor_get(v_x_1390_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_x_1390_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1507_ = v_x_1390_;
v_isShared_1508_ = v_isSharedCheck_1513_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_x_1505_);
lean_dec(v_x_1390_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1513_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1509_ = lean_apply_1(v_f_1389_, v_x_1505_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1509_);
v___x_1511_ = v___x_1507_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapFnBody(lean_object* v_f_1514_, lean_object* v_x_1515_){
_start:
{
switch(lean_obj_tag(v_x_1515_))
{
case 0:
{
lean_object* v_x_1516_; lean_object* v_ty_1517_; lean_object* v_e_1518_; lean_object* v_b_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1528_; 
v_x_1516_ = lean_ctor_get(v_x_1515_, 0);
v_ty_1517_ = lean_ctor_get(v_x_1515_, 1);
v_e_1518_ = lean_ctor_get(v_x_1515_, 2);
v_b_1519_ = lean_ctor_get(v_x_1515_, 3);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_x_1515_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1521_ = v_x_1515_;
v_isShared_1522_ = v_isSharedCheck_1528_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_b_1519_);
lean_inc(v_e_1518_);
lean_inc(v_ty_1517_);
lean_inc(v_x_1516_);
lean_dec(v_x_1515_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1528_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1526_; 
lean_inc_ref(v_f_1514_);
v___x_1523_ = l_Lean_IR_MapVars_mapExpr(v_f_1514_, v_e_1518_);
v___x_1524_ = l_Lean_IR_MapVars_mapFnBody(v_f_1514_, v_b_1519_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 3, v___x_1524_);
lean_ctor_set(v___x_1521_, 2, v___x_1523_);
v___x_1526_ = v___x_1521_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_x_1516_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_ty_1517_);
lean_ctor_set(v_reuseFailAlloc_1527_, 2, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1527_, 3, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
case 1:
{
lean_object* v_j_1529_; lean_object* v_xs_1530_; lean_object* v_v_1531_; lean_object* v_b_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1541_; 
v_j_1529_ = lean_ctor_get(v_x_1515_, 0);
v_xs_1530_ = lean_ctor_get(v_x_1515_, 1);
v_v_1531_ = lean_ctor_get(v_x_1515_, 2);
v_b_1532_ = lean_ctor_get(v_x_1515_, 3);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_x_1515_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1534_ = v_x_1515_;
v_isShared_1535_ = v_isSharedCheck_1541_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_b_1532_);
lean_inc(v_v_1531_);
lean_inc(v_xs_1530_);
lean_inc(v_j_1529_);
lean_dec(v_x_1515_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1541_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1539_; 
lean_inc_ref(v_f_1514_);
v___x_1536_ = l_Lean_IR_MapVars_mapFnBody(v_f_1514_, v_v_1531_);
v___x_1537_ = l_Lean_IR_MapVars_mapFnBody(v_f_1514_, v_b_1532_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 3, v___x_1537_);
lean_ctor_set(v___x_1534_, 2, v___x_1536_);
v___x_1539_ = v___x_1534_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_j_1529_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_xs_1530_);
lean_ctor_set(v_reuseFailAlloc_1540_, 2, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1540_, 3, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
case 2:
{
lean_object* v_x_1542_; lean_object* v_i_1543_; lean_object* v_y_1544_; lean_object* v_b_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1565_; 
v_x_1542_ = lean_ctor_get(v_x_1515_, 0);
v_i_1543_ = lean_ctor_get(v_x_1515_, 1);
v_y_1544_ = lean_ctor_get(v_x_1515_, 2);
v_b_1545_ = lean_ctor_get(v_x_1515_, 3);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_x_1515_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1547_ = v_x_1515_;
v_isShared_1548_ = v_isSharedCheck_1565_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_b_1545_);
lean_inc(v_y_1544_);
lean_inc(v_i_1543_);
lean_inc(v_x_1542_);
lean_dec(v_x_1515_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1565_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v___y_1551_; 
lean_inc_ref(v_f_1514_);
v___x_1549_ = lean_apply_1(v_f_1514_, v_x_1542_);
if (lean_obj_tag(v_y_1544_) == 0)
{
lean_object* v_id_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1564_; 
v_id_1556_ = lean_ctor_get(v_y_1544_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_y_1544_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1558_ = v_y_1544_;
v_isShared_1559_ = v_isSharedCheck_1564_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_id_1556_);
lean_dec(v_y_1544_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1564_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1560_; lean_object* v___x_1562_; 
lean_inc_ref(v_f_1514_);
v___x_1560_ = lean_apply_1(v_f_1514_, v_id_1556_);
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 0, v___x_1560_);
v___x_1562_ = v___x_1558_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
v___y_1551_ = v___x_1562_;
goto v___jp_1550_;
}
}
}
else
{
v___y_1551_ = v_y_1544_;
goto v___jp_1550_;
}
v___jp_1550_:
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1552_ = l_Lean_IR_MapVars_mapFnBody(v_f_1514_, v_b_1545_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 3, v___x_1552_);
lean_ctor_set(v___x_1547_, 2, v___y_1551_);
lean_ctor_set(v___x_1547_, 0, v___x_1549_);
v___x_1554_ = v___x_1547_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_i_1543_);
lean_ctor_set(v_reuseFailAlloc_1555_, 2, v___y_1551_);
lean_ctor_set(v_reuseFailAlloc_1555_, 3, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
case 3:
{
lean_object* v_x_1566_; lean_object* v_cidx_1567_; lean_object* v_b_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1577_; 
v_x_1566_ = lean_ctor_get(v_x_1515_, 0);
v_cidx_1567_ = lean_ctor_get(v_x_1515_, 1);
v_b_1568_ = lean_ctor_get(v_x_1515_, 2);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_x_1515_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1570_ = v_x_1515_;
v_isShared_1571_ = v_isSharedCheck_1577_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_b_1568_);
lean_inc(v_cidx_1567_);
lean_inc(v_x_1566_);
lean_dec(v_x_1515_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1577_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1575_; 
lean_inc_ref(v_f_1514_);
v___x_1572_ = lean_apply_1(v_f_1514_, v_x_1566_);
v___x_1573_ = l_Lean_IR_MapVars_mapFnBody(v_f_1514_, v_b_1568_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 2, v___x_1573_);
lean_ctor_set(v___x_1570_, 0, v___x_1572_);
v___x_1575_ = v___x_1570_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_cidx_1567_);
lean_ctor_set(v_reuseFailAlloc_1576_, 2, v___x_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
case 4:
{
lean_object* v_x_1578_; lean_object* v_i_1579_; lean_object* v_y_1580_; lean_object* v_b_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1591_; 
v_x_1578_ = lean_ctor_get(v_x_1515_, 0);
v_i_1579_ = lean_ctor_get(v_x_1515_, 1);
v_y_1580_ = lean_ctor_get(v_x_1515_, 2);
v_b_1581_ = lean_ctor_get(v_x_1515_, 3);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_x_1515_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1583_ = v_x_1515_;
v_isShared_1584_ = v_isSharedCheck_1591_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_b_1581_);
lean_inc(v_y_1580_);
lean_inc(v_i_1579_);
lean_inc(v_x_1578_);
lean_dec(v_x_1515_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1591_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1589_; 
lean_inc_ref_n(v_f_1514_, 2);
v___x_1585_ = lean_apply_1(v_f_1514_, v_x_1578_);
v___x_1586_ = lean_apply_1(v_f_1514_, v_y_1580_);
v___x_1587_ = l_Lean_IR_MapVars_mapFnBody(v_f_1514_, v_b_1581_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 3, v___x_1587_);
lean_ctor_set(v___x_1583_, 2, v___x_1586_);
lean_ctor_set(v___x_1583_, 0, v___x_1585_);
v___x_1589_ = v___x_1583_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_i_1579_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1590_, 3, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
case 5:
{
lean_object* v_x_1592_; lean_object* v_i_1593_; lean_object* v_offset_1594_; lean_object* v_y_1595_; lean_object* v_ty_1596_; lean_object* v_b_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1607_; 
v_x_1592_ = lean_ctor_get(v_x_1515_, 0);
v_i_1593_ = lean_ctor_get(v_x_1515_, 1);
v_offset_1594_ = lean_ctor_get(v_x_1515_, 2);
v_y_1595_ = lean_ctor_get(v_x_1515_, 3);
v_ty_1596_ = lean_ctor_get(v_x_1515_, 4);
v_b_1597_ = lean_ctor_get(v_x_1515_, 5);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_x_1515_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1599_ = v_x_1515_;
v_isShared_1600_ = v_isSharedCheck_1607_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_b_1597_);
lean_inc(v_ty_1596_);
lean_inc(v_y_1595_);
lean_inc(v_offset_1594_);
lean_inc(v_i_1593_);
lean_inc(v_x_1592_);
lean_dec(v_x_1515_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1607_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
lean_inc_ref_n(v_f_1514_, 2);
v___x_1601_ = lean_apply_1(v_f_1514_, v_x_1592_);
v___x_1602_ = lean_apply_1(v_f_1514_, v_y_1595_);
v___x_1603_ = l_Lean_IR_MapVars_mapFnBody(v_f_1514_, v_b_1597_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 5, v___x_1603_);
lean_ctor_set(v___x_1599_, 3, v___x_1602_);
lean_ctor_set(v___x_1599_, 0, v___x_1601_);
v___x_1605_ = v___x_1599_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1601_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_i_1593_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_offset_1594_);
lean_ctor_set(v_reuseFailAlloc_1606_, 3, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1606_, 4, v_ty_1596_);
lean_ctor_set(v_reuseFailAlloc_1606_, 5, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
case 6:
{
lean_object* v_x_1608_; lean_object* v_n_1609_; uint8_t v_c_1610_; uint8_t v_persistent_1611_; lean_object* v_b_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1621_; 
v_x_1608_ = lean_ctor_get(v_x_1515_, 0);
v_n_1609_ = lean_ctor_get(v_x_1515_, 1);
v_c_1610_ = lean_ctor_get_uint8(v_x_1515_, sizeof(void*)*3);
v_persistent_1611_ = lean_ctor_get_uint8(v_x_1515_, sizeof(void*)*3 + 1);
v_b_1612_ = lean_ctor_get(v_x_1515_, 2);
v_isSharedCheck_1621_ = !lean_is_exclusive(v_x_1515_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1614_ = v_x_1515_;
v_isShared_1615_ = v_isSharedCheck_1621_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_b_1612_);
lean_inc(v_n_1609_);
lean_inc(v_x_1608_);
lean_dec(v_x_1515_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1621_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
lean_inc_ref(v_f_1514_);
v___x_1616_ = lean_apply_1(v_f_1514_, v_x_1608_);
v___x_1617_ = l_Lean_IR_MapVars_mapFnBody(v_f_1514_, v_b_1612_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 2, v___x_1617_);
lean_ctor_set(v___x_1614_, 0, v___x_1616_);
v___x_1619_ = v___x_1614_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_n_1609_);
lean_ctor_set(v_reuseFailAlloc_1620_, 2, v___x_1617_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*3, v_c_1610_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*3 + 1, v_persistent_1611_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
case 7:
{
lean_object* v_x_1622_; lean_object* v_n_1623_; uint8_t v_c_1624_; uint8_t v_persistent_1625_; lean_object* v_b_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1635_; 
v_x_1622_ = lean_ctor_get(v_x_1515_, 0);
v_n_1623_ = lean_ctor_get(v_x_1515_, 1);
v_c_1624_ = lean_ctor_get_uint8(v_x_1515_, sizeof(void*)*3);
v_persistent_1625_ = lean_ctor_get_uint8(v_x_1515_, sizeof(void*)*3 + 1);
v_b_1626_ = lean_ctor_get(v_x_1515_, 2);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_x_1515_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1628_ = v_x_1515_;
v_isShared_1629_ = v_isSharedCheck_1635_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_b_1626_);
lean_inc(v_n_1623_);
lean_inc(v_x_1622_);
lean_dec(v_x_1515_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1635_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
lean_inc_ref(v_f_1514_);
v___x_1630_ = lean_apply_1(v_f_1514_, v_x_1622_);
v___x_1631_ = l_Lean_IR_MapVars_mapFnBody(v_f_1514_, v_b_1626_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 2, v___x_1631_);
lean_ctor_set(v___x_1628_, 0, v___x_1630_);
v___x_1633_ = v___x_1628_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_n_1623_);
lean_ctor_set(v_reuseFailAlloc_1634_, 2, v___x_1631_);
lean_ctor_set_uint8(v_reuseFailAlloc_1634_, sizeof(void*)*3, v_c_1624_);
lean_ctor_set_uint8(v_reuseFailAlloc_1634_, sizeof(void*)*3 + 1, v_persistent_1625_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
case 8:
{
lean_object* v_x_1636_; lean_object* v_b_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1646_; 
v_x_1636_ = lean_ctor_get(v_x_1515_, 0);
v_b_1637_ = lean_ctor_get(v_x_1515_, 1);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_x_1515_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1639_ = v_x_1515_;
v_isShared_1640_ = v_isSharedCheck_1646_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_b_1637_);
lean_inc(v_x_1636_);
lean_dec(v_x_1515_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1646_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
lean_inc_ref(v_f_1514_);
v___x_1641_ = lean_apply_1(v_f_1514_, v_x_1636_);
v___x_1642_ = l_Lean_IR_MapVars_mapFnBody(v_f_1514_, v_b_1637_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 1, v___x_1642_);
lean_ctor_set(v___x_1639_, 0, v___x_1641_);
v___x_1644_ = v___x_1639_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
case 9:
{
lean_object* v_tid_1647_; lean_object* v_x_1648_; lean_object* v_xType_1649_; lean_object* v_cs_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1661_; 
v_tid_1647_ = lean_ctor_get(v_x_1515_, 0);
v_x_1648_ = lean_ctor_get(v_x_1515_, 1);
v_xType_1649_ = lean_ctor_get(v_x_1515_, 2);
v_cs_1650_ = lean_ctor_get(v_x_1515_, 3);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_x_1515_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1652_ = v_x_1515_;
v_isShared_1653_ = v_isSharedCheck_1661_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_cs_1650_);
lean_inc(v_xType_1649_);
lean_inc(v_x_1648_);
lean_inc(v_tid_1647_);
lean_dec(v_x_1515_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1661_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; size_t v_sz_1655_; size_t v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1659_; 
lean_inc_ref(v_f_1514_);
v___x_1654_ = lean_apply_1(v_f_1514_, v_x_1648_);
v_sz_1655_ = lean_array_size(v_cs_1650_);
v___x_1656_ = ((size_t)0ULL);
v___x_1657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(v_f_1514_, v_sz_1655_, v___x_1656_, v_cs_1650_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 3, v___x_1657_);
lean_ctor_set(v___x_1652_, 1, v___x_1654_);
v___x_1659_ = v___x_1652_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_tid_1647_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_xType_1649_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
case 10:
{
lean_object* v_x_1662_; 
v_x_1662_ = lean_ctor_get(v_x_1515_, 0);
lean_inc(v_x_1662_);
if (lean_obj_tag(v_x_1662_) == 0)
{
lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1678_; 
v_isSharedCheck_1678_ = !lean_is_exclusive(v_x_1515_);
if (v_isSharedCheck_1678_ == 0)
{
lean_object* v_unused_1679_; 
v_unused_1679_ = lean_ctor_get(v_x_1515_, 0);
lean_dec(v_unused_1679_);
v___x_1664_ = v_x_1515_;
v_isShared_1665_ = v_isSharedCheck_1678_;
goto v_resetjp_1663_;
}
else
{
lean_dec(v_x_1515_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1678_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v_id_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1677_; 
v_id_1666_ = lean_ctor_get(v_x_1662_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_x_1662_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1668_ = v_x_1662_;
v_isShared_1669_ = v_isSharedCheck_1677_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_id_1666_);
lean_dec(v_x_1662_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1677_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1670_ = lean_apply_1(v_f_1514_, v_id_1666_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v___x_1670_);
v___x_1672_ = v___x_1668_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1674_; 
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1672_);
v___x_1674_ = v___x_1664_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_1514_);
return v_x_1515_;
}
}
case 11:
{
lean_object* v_j_1680_; lean_object* v_ys_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1689_; 
v_j_1680_ = lean_ctor_get(v_x_1515_, 0);
v_ys_1681_ = lean_ctor_get(v_x_1515_, 1);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_x_1515_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1683_ = v_x_1515_;
v_isShared_1684_ = v_isSharedCheck_1689_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_ys_1681_);
lean_inc(v_j_1680_);
lean_dec(v_x_1515_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1689_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1685_ = l_Lean_IR_MapVars_mapArgs(v_f_1514_, v_ys_1681_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 1, v___x_1685_);
v___x_1687_ = v___x_1683_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_j_1680_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
default: 
{
lean_dec_ref(v_f_1514_);
return v_x_1515_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(lean_object* v_f_1690_, size_t v_sz_1691_, size_t v_i_1692_, lean_object* v_bs_1693_){
_start:
{
uint8_t v___x_1694_; 
v___x_1694_ = lean_usize_dec_lt(v_i_1692_, v_sz_1691_);
if (v___x_1694_ == 0)
{
lean_dec_ref(v_f_1690_);
return v_bs_1693_;
}
else
{
lean_object* v_v_1695_; lean_object* v___x_1696_; lean_object* v_bs_x27_1697_; lean_object* v___y_1699_; 
v_v_1695_ = lean_array_uget(v_bs_1693_, v_i_1692_);
v___x_1696_ = lean_unsigned_to_nat(0u);
v_bs_x27_1697_ = lean_array_uset(v_bs_1693_, v_i_1692_, v___x_1696_);
if (lean_obj_tag(v_v_1695_) == 0)
{
lean_object* v_info_1704_; lean_object* v_b_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1713_; 
v_info_1704_ = lean_ctor_get(v_v_1695_, 0);
v_b_1705_ = lean_ctor_get(v_v_1695_, 1);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_v_1695_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1707_ = v_v_1695_;
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_b_1705_);
lean_inc(v_info_1704_);
lean_dec(v_v_1695_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1711_; 
lean_inc_ref(v_f_1690_);
v___x_1709_ = l_Lean_IR_MapVars_mapFnBody(v_f_1690_, v_b_1705_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 1, v___x_1709_);
v___x_1711_ = v___x_1707_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_info_1704_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
v___y_1699_ = v___x_1711_;
goto v___jp_1698_;
}
}
}
else
{
lean_object* v_b_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1722_; 
v_b_1714_ = lean_ctor_get(v_v_1695_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_v_1695_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1716_ = v_v_1695_;
v_isShared_1717_ = v_isSharedCheck_1722_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_b_1714_);
lean_dec(v_v_1695_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1722_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1720_; 
lean_inc_ref(v_f_1690_);
v___x_1718_ = l_Lean_IR_MapVars_mapFnBody(v_f_1690_, v_b_1714_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v___x_1718_);
v___x_1720_ = v___x_1716_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
v___y_1699_ = v___x_1720_;
goto v___jp_1698_;
}
}
}
v___jp_1698_:
{
size_t v___x_1700_; size_t v___x_1701_; lean_object* v___x_1702_; 
v___x_1700_ = ((size_t)1ULL);
v___x_1701_ = lean_usize_add(v_i_1692_, v___x_1700_);
v___x_1702_ = lean_array_uset(v_bs_x27_1697_, v_i_1692_, v___y_1699_);
v_i_1692_ = v___x_1701_;
v_bs_1693_ = v___x_1702_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0___boxed(lean_object* v_f_1723_, lean_object* v_sz_1724_, lean_object* v_i_1725_, lean_object* v_bs_1726_){
_start:
{
size_t v_sz_boxed_1727_; size_t v_i_boxed_1728_; lean_object* v_res_1729_; 
v_sz_boxed_1727_ = lean_unbox_usize(v_sz_1724_);
lean_dec(v_sz_1724_);
v_i_boxed_1728_ = lean_unbox_usize(v_i_1725_);
lean_dec(v_i_1725_);
v_res_1729_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(v_f_1723_, v_sz_boxed_1727_, v_i_boxed_1728_, v_bs_1726_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_mapVars(lean_object* v_f_1730_, lean_object* v_b_1731_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_IR_MapVars_mapFnBody(v_f_1730_, v_b_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lam__0(lean_object* v_x_1733_, lean_object* v_y_1734_, lean_object* v_z_1735_){
_start:
{
uint8_t v___x_1736_; 
v___x_1736_ = l_Lean_IR_instBEqVarId_beq(v_x_1733_, v_z_1735_);
if (v___x_1736_ == 0)
{
lean_inc(v_z_1735_);
return v_z_1735_;
}
else
{
lean_inc(v_y_1734_);
return v_y_1734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lam__0___boxed(lean_object* v_x_1737_, lean_object* v_y_1738_, lean_object* v_z_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_IR_FnBody_replaceVar___lam__0(v_x_1737_, v_y_1738_, v_z_1739_);
lean_dec(v_z_1739_);
lean_dec(v_y_1738_);
lean_dec(v_x_1737_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar(lean_object* v_x_1741_, lean_object* v_y_1742_, lean_object* v_b_1743_){
_start:
{
lean_object* v___f_1744_; lean_object* v___x_1745_; 
v___f_1744_ = lean_alloc_closure((void*)(l_Lean_IR_FnBody_replaceVar___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1744_, 0, v_x_1741_);
lean_closure_set(v___f_1744_, 1, v_y_1742_);
v___x_1745_ = l_Lean_IR_MapVars_mapFnBody(v___f_1744_, v_b_1743_);
return v___x_1745_;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_NormIds(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
