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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_inc(v_m_735_);
lean_inc(v_a_736_);
v___x_740_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_737_, v_x_733_, v_a_736_, v_m_735_);
v___x_741_ = lean_apply_3(v_k_734_, v_a_736_, v___x_740_, v___x_739_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg___boxed(lean_object* v_x_742_, lean_object* v_k_743_, lean_object* v_m_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_IR_NormalizeIds_withVar___redArg(v_x_742_, v_k_743_, v_m_744_, v_a_745_);
lean_dec(v_m_744_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar(lean_object* v_00_u03b1_747_, lean_object* v_x_748_, lean_object* v_k_749_, lean_object* v_m_750_, lean_object* v_a_751_){
_start:
{
lean_object* v___f_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___f_752_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_753_ = lean_unsigned_to_nat(1u);
v___x_754_ = lean_nat_add(v_a_751_, v___x_753_);
lean_inc(v_m_750_);
lean_inc(v_a_751_);
v___x_755_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_752_, v_x_748_, v_a_751_, v_m_750_);
v___x_756_ = lean_apply_3(v_k_749_, v_a_751_, v___x_755_, v___x_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___boxed(lean_object* v_00_u03b1_757_, lean_object* v_x_758_, lean_object* v_k_759_, lean_object* v_m_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_IR_NormalizeIds_withVar(v_00_u03b1_757_, v_x_758_, v_k_759_, v_m_760_, v_a_761_);
lean_dec(v_m_760_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___redArg(lean_object* v_x_763_, lean_object* v_k_764_, lean_object* v_m_765_, lean_object* v_a_766_){
_start:
{
lean_object* v___f_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___f_767_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_768_ = lean_unsigned_to_nat(1u);
v___x_769_ = lean_nat_add(v_a_766_, v___x_768_);
lean_inc(v_m_765_);
lean_inc(v_a_766_);
v___x_770_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_767_, v_x_763_, v_a_766_, v_m_765_);
v___x_771_ = lean_apply_3(v_k_764_, v_a_766_, v___x_770_, v___x_769_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___redArg___boxed(lean_object* v_x_772_, lean_object* v_k_773_, lean_object* v_m_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_IR_NormalizeIds_withJP___redArg(v_x_772_, v_k_773_, v_m_774_, v_a_775_);
lean_dec(v_m_774_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP(lean_object* v_00_u03b1_777_, lean_object* v_x_778_, lean_object* v_k_779_, lean_object* v_m_780_, lean_object* v_a_781_){
_start:
{
lean_object* v___f_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___f_782_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_783_ = lean_unsigned_to_nat(1u);
v___x_784_ = lean_nat_add(v_a_781_, v___x_783_);
lean_inc(v_m_780_);
lean_inc(v_a_781_);
v___x_785_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_782_, v_x_778_, v_a_781_, v_m_780_);
v___x_786_ = lean_apply_3(v_k_779_, v_a_781_, v___x_785_, v___x_784_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___boxed(lean_object* v_00_u03b1_787_, lean_object* v_x_788_, lean_object* v_k_789_, lean_object* v_m_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_IR_NormalizeIds_withJP(v_00_u03b1_787_, v_x_788_, v_k_789_, v_m_790_, v_a_791_);
lean_dec(v_m_790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__0(lean_object* v_fst_793_, lean_object* v_x_794_){
_start:
{
lean_object* v_x_795_; uint8_t v_borrow_796_; lean_object* v_ty_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_805_; 
v_x_795_ = lean_ctor_get(v_x_794_, 0);
v_borrow_796_ = lean_ctor_get_uint8(v_x_794_, sizeof(void*)*2);
v_ty_797_ = lean_ctor_get(v_x_794_, 1);
v_isSharedCheck_805_ = !lean_is_exclusive(v_x_794_);
if (v_isSharedCheck_805_ == 0)
{
v___x_799_ = v_x_794_;
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_ty_797_);
lean_inc(v_x_795_);
lean_dec(v_x_794_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_801_ = l_Lean_IR_NormalizeIds_normIndex(v_x_795_, v_fst_793_);
lean_dec(v_x_795_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_801_);
v___x_803_ = v___x_799_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_ty_797_);
lean_ctor_set_uint8(v_reuseFailAlloc_804_, sizeof(void*)*2, v_borrow_796_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed(lean_object* v_fst_806_, lean_object* v_x_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_IR_NormalizeIds_withParams___redArg___lam__0(v_fst_806_, v_x_807_);
lean_dec(v_fst_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__2(lean_object* v___f_809_, lean_object* v_m_810_, lean_object* v_p_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v_x_813_ = lean_ctor_get(v_p_811_, 0);
lean_inc(v_x_813_);
lean_dec_ref(v_p_811_);
v___x_814_ = lean_unsigned_to_nat(1u);
v___x_815_ = lean_nat_add(v___y_812_, v___x_814_);
v___x_816_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_809_, v_x_813_, v___y_812_, v_m_810_);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v___x_815_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg(lean_object* v_ps_865_, lean_object* v_k_866_, lean_object* v_m_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___x_869_; lean_object* v_fst_871_; lean_object* v_snd_872_; lean_object* v___y_879_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v___x_869_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__9));
v___x_882_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__19));
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = lean_array_get_size(v_ps_865_);
v___x_885_ = lean_nat_dec_lt(v___x_883_, v___x_884_);
if (v___x_885_ == 0)
{
lean_inc(v_m_867_);
v_fst_871_ = v_m_867_;
v_snd_872_ = v_a_868_;
goto v___jp_870_;
}
else
{
lean_object* v___f_886_; uint8_t v___x_887_; 
v___f_886_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__20));
v___x_887_ = lean_nat_dec_le(v___x_884_, v___x_884_);
if (v___x_887_ == 0)
{
if (v___x_885_ == 0)
{
lean_inc(v_m_867_);
v_fst_871_ = v_m_867_;
v_snd_872_ = v_a_868_;
goto v___jp_870_;
}
else
{
size_t v___x_888_; size_t v___x_889_; lean_object* v___x_793__overap_890_; lean_object* v___x_891_; 
v___x_888_ = ((size_t)0ULL);
v___x_889_ = lean_usize_of_nat(v___x_884_);
lean_inc(v_m_867_);
lean_inc_ref(v_ps_865_);
v___x_793__overap_890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_882_, v___f_886_, v_ps_865_, v___x_888_, v___x_889_, v_m_867_);
v___x_891_ = lean_apply_1(v___x_793__overap_890_, v_a_868_);
v___y_879_ = v___x_891_;
goto v___jp_878_;
}
}
else
{
size_t v___x_892_; size_t v___x_893_; lean_object* v___x_798__overap_894_; lean_object* v___x_895_; 
v___x_892_ = ((size_t)0ULL);
v___x_893_ = lean_usize_of_nat(v___x_884_);
lean_inc(v_m_867_);
lean_inc_ref(v_ps_865_);
v___x_798__overap_894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_882_, v___f_886_, v_ps_865_, v___x_892_, v___x_893_, v_m_867_);
v___x_895_ = lean_apply_1(v___x_798__overap_894_, v_a_868_);
v___y_879_ = v___x_895_;
goto v___jp_878_;
}
}
v___jp_870_:
{
lean_object* v___f_873_; size_t v_sz_874_; size_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
lean_inc(v_fst_871_);
v___f_873_ = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_873_, 0, v_fst_871_);
v_sz_874_ = lean_array_size(v_ps_865_);
v___x_875_ = ((size_t)0ULL);
v___x_876_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_869_, v___f_873_, v_sz_874_, v___x_875_, v_ps_865_);
v___x_877_ = lean_apply_3(v_k_866_, v___x_876_, v_fst_871_, v_snd_872_);
return v___x_877_;
}
v___jp_878_:
{
lean_object* v_fst_880_; lean_object* v_snd_881_; 
v_fst_880_ = lean_ctor_get(v___y_879_, 0);
lean_inc(v_fst_880_);
v_snd_881_ = lean_ctor_get(v___y_879_, 1);
lean_inc(v_snd_881_);
lean_dec_ref(v___y_879_);
v_fst_871_ = v_fst_880_;
v_snd_872_ = v_snd_881_;
goto v___jp_870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___boxed(lean_object* v_ps_896_, lean_object* v_k_897_, lean_object* v_m_898_, lean_object* v_a_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_IR_NormalizeIds_withParams___redArg(v_ps_896_, v_k_897_, v_m_898_, v_a_899_);
lean_dec(v_m_898_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams(lean_object* v_00_u03b1_901_, lean_object* v_ps_902_, lean_object* v_k_903_, lean_object* v_m_904_, lean_object* v_a_905_){
_start:
{
lean_object* v___x_906_; lean_object* v_fst_908_; lean_object* v_snd_909_; lean_object* v___y_916_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_906_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__9));
v___x_919_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__19));
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = lean_array_get_size(v_ps_902_);
v___x_922_ = lean_nat_dec_lt(v___x_920_, v___x_921_);
if (v___x_922_ == 0)
{
lean_inc(v_m_904_);
v_fst_908_ = v_m_904_;
v_snd_909_ = v_a_905_;
goto v___jp_907_;
}
else
{
lean_object* v___f_923_; uint8_t v___x_924_; 
v___f_923_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__20));
v___x_924_ = lean_nat_dec_le(v___x_921_, v___x_921_);
if (v___x_924_ == 0)
{
if (v___x_922_ == 0)
{
lean_inc(v_m_904_);
v_fst_908_ = v_m_904_;
v_snd_909_ = v_a_905_;
goto v___jp_907_;
}
else
{
size_t v___x_925_; size_t v___x_926_; lean_object* v___x_975__overap_927_; lean_object* v___x_928_; 
v___x_925_ = ((size_t)0ULL);
v___x_926_ = lean_usize_of_nat(v___x_921_);
lean_inc(v_m_904_);
lean_inc_ref(v_ps_902_);
v___x_975__overap_927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_919_, v___f_923_, v_ps_902_, v___x_925_, v___x_926_, v_m_904_);
v___x_928_ = lean_apply_1(v___x_975__overap_927_, v_a_905_);
v___y_916_ = v___x_928_;
goto v___jp_915_;
}
}
else
{
size_t v___x_929_; size_t v___x_930_; lean_object* v___x_978__overap_931_; lean_object* v___x_932_; 
v___x_929_ = ((size_t)0ULL);
v___x_930_ = lean_usize_of_nat(v___x_921_);
lean_inc(v_m_904_);
lean_inc_ref(v_ps_902_);
v___x_978__overap_931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_919_, v___f_923_, v_ps_902_, v___x_929_, v___x_930_, v_m_904_);
v___x_932_ = lean_apply_1(v___x_978__overap_931_, v_a_905_);
v___y_916_ = v___x_932_;
goto v___jp_915_;
}
}
v___jp_907_:
{
lean_object* v___f_910_; size_t v_sz_911_; size_t v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
lean_inc(v_fst_908_);
v___f_910_ = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_910_, 0, v_fst_908_);
v_sz_911_ = lean_array_size(v_ps_902_);
v___x_912_ = ((size_t)0ULL);
v___x_913_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_906_, v___f_910_, v_sz_911_, v___x_912_, v_ps_902_);
v___x_914_ = lean_apply_3(v_k_903_, v___x_913_, v_fst_908_, v_snd_909_);
return v___x_914_;
}
v___jp_915_:
{
lean_object* v_fst_917_; lean_object* v_snd_918_; 
v_fst_917_ = lean_ctor_get(v___y_916_, 0);
lean_inc(v_fst_917_);
v_snd_918_ = lean_ctor_get(v___y_916_, 1);
lean_inc(v_snd_918_);
lean_dec_ref(v___y_916_);
v_fst_908_ = v_fst_917_;
v_snd_909_ = v_snd_918_;
goto v___jp_907_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___boxed(lean_object* v_00_u03b1_933_, lean_object* v_ps_934_, lean_object* v_k_935_, lean_object* v_m_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_IR_NormalizeIds_withParams(v_00_u03b1_933_, v_ps_934_, v_k_935_, v_m_936_, v_a_937_);
lean_dec(v_m_936_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_instMonadLiftMN___lam__0(lean_object* v_00_u03b1_939_, lean_object* v_x_940_, lean_object* v_m_941_, lean_object* v___y_942_){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_apply_1(v_x_940_, v_m_941_);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v___y_942_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(lean_object* v_fst_947_, size_t v_sz_948_, size_t v_i_949_, lean_object* v_bs_950_){
_start:
{
uint8_t v___x_951_; 
v___x_951_ = lean_usize_dec_lt(v_i_949_, v_sz_948_);
if (v___x_951_ == 0)
{
return v_bs_950_;
}
else
{
lean_object* v_v_952_; lean_object* v_x_953_; uint8_t v_borrow_954_; lean_object* v_ty_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_969_; 
v_v_952_ = lean_array_uget(v_bs_950_, v_i_949_);
v_x_953_ = lean_ctor_get(v_v_952_, 0);
v_borrow_954_ = lean_ctor_get_uint8(v_v_952_, sizeof(void*)*2);
v_ty_955_ = lean_ctor_get(v_v_952_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v_v_952_);
if (v_isSharedCheck_969_ == 0)
{
v___x_957_ = v_v_952_;
v_isShared_958_ = v_isSharedCheck_969_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_ty_955_);
lean_inc(v_x_953_);
lean_dec(v_v_952_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_969_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v_bs_x27_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_959_ = lean_unsigned_to_nat(0u);
v_bs_x27_960_ = lean_array_uset(v_bs_950_, v_i_949_, v___x_959_);
v___x_961_ = l_Lean_IR_NormalizeIds_normIndex(v_x_953_, v_fst_947_);
lean_dec(v_x_953_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_961_);
v___x_963_ = v___x_957_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_ty_955_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, sizeof(void*)*2, v_borrow_954_);
v___x_963_ = v_reuseFailAlloc_968_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
size_t v___x_964_; size_t v___x_965_; lean_object* v___x_966_; 
v___x_964_ = ((size_t)1ULL);
v___x_965_ = lean_usize_add(v_i_949_, v___x_964_);
v___x_966_ = lean_array_uset(v_bs_x27_960_, v_i_949_, v___x_963_);
v_i_949_ = v___x_965_;
v_bs_950_ = v___x_966_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0___boxed(lean_object* v_fst_970_, lean_object* v_sz_971_, lean_object* v_i_972_, lean_object* v_bs_973_){
_start:
{
size_t v_sz_boxed_974_; size_t v_i_boxed_975_; lean_object* v_res_976_; 
v_sz_boxed_974_ = lean_unbox_usize(v_sz_971_);
lean_dec(v_sz_971_);
v_i_boxed_975_ = lean_unbox_usize(v_i_972_);
lean_dec(v_i_972_);
v_res_976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(v_fst_970_, v_sz_boxed_974_, v_i_boxed_975_, v_bs_973_);
lean_dec(v_fst_970_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(lean_object* v_as_977_, size_t v_i_978_, size_t v_stop_979_, lean_object* v_b_980_, lean_object* v___y_981_){
_start:
{
uint8_t v___x_982_; 
v___x_982_ = lean_usize_dec_eq(v_i_978_, v_stop_979_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v_x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; size_t v___x_988_; size_t v___x_989_; 
v___x_983_ = lean_array_uget_borrowed(v_as_977_, v_i_978_);
v_x_984_ = lean_ctor_get(v___x_983_, 0);
v___x_985_ = lean_unsigned_to_nat(1u);
v___x_986_ = lean_nat_add(v___y_981_, v___x_985_);
lean_inc(v_x_984_);
v___x_987_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_x_984_, v___y_981_, v_b_980_);
v___x_988_ = ((size_t)1ULL);
v___x_989_ = lean_usize_add(v_i_978_, v___x_988_);
v_i_978_ = v___x_989_;
v_b_980_ = v___x_987_;
v___y_981_ = v___x_986_;
goto _start;
}
else
{
lean_object* v___x_991_; 
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_b_980_);
lean_ctor_set(v___x_991_, 1, v___y_981_);
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1___boxed(lean_object* v_as_992_, lean_object* v_i_993_, lean_object* v_stop_994_, lean_object* v_b_995_, lean_object* v___y_996_){
_start:
{
size_t v_i_boxed_997_; size_t v_stop_boxed_998_; lean_object* v_res_999_; 
v_i_boxed_997_ = lean_unbox_usize(v_i_993_);
lean_dec(v_i_993_);
v_stop_boxed_998_ = lean_unbox_usize(v_stop_994_);
lean_dec(v_stop_994_);
v_res_999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_as_992_, v_i_boxed_997_, v_stop_boxed_998_, v_b_995_, v___y_996_);
lean_dec_ref(v_as_992_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normFnBody(lean_object* v_x_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
switch(lean_obj_tag(v_x_1000_))
{
case 0:
{
lean_object* v_x_1003_; lean_object* v_ty_1004_; lean_object* v_e_1005_; lean_object* v_b_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1027_; 
v_x_1003_ = lean_ctor_get(v_x_1000_, 0);
v_ty_1004_ = lean_ctor_get(v_x_1000_, 1);
v_e_1005_ = lean_ctor_get(v_x_1000_, 2);
v_b_1006_ = lean_ctor_get(v_x_1000_, 3);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_x_1000_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1008_ = v_x_1000_;
v_isShared_1009_ = v_isSharedCheck_1027_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_b_1006_);
lean_inc(v_e_1005_);
lean_inc(v_ty_1004_);
lean_inc(v_x_1003_);
lean_dec(v_x_1000_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1027_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v_fst_1014_; lean_object* v_snd_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1026_; 
v___x_1010_ = lean_unsigned_to_nat(1u);
v___x_1011_ = lean_nat_add(v_a_1002_, v___x_1010_);
lean_inc(v_a_1001_);
lean_inc(v_a_1002_);
v___x_1012_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_x_1003_, v_a_1002_, v_a_1001_);
v___x_1013_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1006_, v___x_1012_, v___x_1011_);
lean_dec(v___x_1012_);
v_fst_1014_ = lean_ctor_get(v___x_1013_, 0);
v_snd_1015_ = lean_ctor_get(v___x_1013_, 1);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1017_ = v___x_1013_;
v_isShared_1018_ = v_isSharedCheck_1026_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_snd_1015_);
lean_inc(v_fst_1014_);
lean_dec(v___x_1013_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1026_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1019_ = l_Lean_IR_NormalizeIds_normExpr(v_e_1005_, v_a_1001_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 3, v_fst_1014_);
lean_ctor_set(v___x_1008_, 2, v___x_1019_);
lean_ctor_set(v___x_1008_, 0, v_a_1002_);
v___x_1021_ = v___x_1008_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1002_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_ty_1004_);
lean_ctor_set(v_reuseFailAlloc_1025_, 2, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1025_, 3, v_fst_1014_);
v___x_1021_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1023_; 
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v___x_1021_);
v___x_1023_ = v___x_1017_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_snd_1015_);
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
}
case 1:
{
lean_object* v_j_1028_; lean_object* v_xs_1029_; lean_object* v_v_1030_; lean_object* v_b_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1074_; 
v_j_1028_ = lean_ctor_get(v_x_1000_, 0);
v_xs_1029_ = lean_ctor_get(v_x_1000_, 1);
v_v_1030_ = lean_ctor_get(v_x_1000_, 2);
v_b_1031_ = lean_ctor_get(v_x_1000_, 3);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_x_1000_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1033_ = v_x_1000_;
v_isShared_1034_ = v_isSharedCheck_1074_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_b_1031_);
lean_inc(v_v_1030_);
lean_inc(v_xs_1029_);
lean_inc(v_j_1028_);
lean_dec(v_x_1000_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1074_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v_fst_1036_; lean_object* v_snd_1037_; lean_object* v___y_1061_; lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1064_ = lean_unsigned_to_nat(0u);
v___x_1065_ = lean_array_get_size(v_xs_1029_);
v___x_1066_ = lean_nat_dec_lt(v___x_1064_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_inc(v_a_1001_);
v_fst_1036_ = v_a_1001_;
v_snd_1037_ = v_a_1002_;
goto v___jp_1035_;
}
else
{
uint8_t v___x_1067_; 
v___x_1067_ = lean_nat_dec_le(v___x_1065_, v___x_1065_);
if (v___x_1067_ == 0)
{
if (v___x_1066_ == 0)
{
lean_inc(v_a_1001_);
v_fst_1036_ = v_a_1001_;
v_snd_1037_ = v_a_1002_;
goto v___jp_1035_;
}
else
{
size_t v___x_1068_; size_t v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = ((size_t)0ULL);
v___x_1069_ = lean_usize_of_nat(v___x_1065_);
lean_inc(v_a_1001_);
v___x_1070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_1029_, v___x_1068_, v___x_1069_, v_a_1001_, v_a_1002_);
v___y_1061_ = v___x_1070_;
goto v___jp_1060_;
}
}
else
{
size_t v___x_1071_; size_t v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = ((size_t)0ULL);
v___x_1072_ = lean_usize_of_nat(v___x_1065_);
lean_inc(v_a_1001_);
v___x_1073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_1029_, v___x_1071_, v___x_1072_, v_a_1001_, v_a_1002_);
v___y_1061_ = v___x_1073_;
goto v___jp_1060_;
}
}
v___jp_1035_:
{
lean_object* v___x_1038_; lean_object* v_fst_1039_; lean_object* v_snd_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v_fst_1045_; lean_object* v_snd_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1059_; 
v___x_1038_ = l_Lean_IR_NormalizeIds_normFnBody(v_v_1030_, v_fst_1036_, v_snd_1037_);
v_fst_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_fst_1039_);
v_snd_1040_ = lean_ctor_get(v___x_1038_, 1);
lean_inc_n(v_snd_1040_, 2);
lean_dec_ref(v___x_1038_);
v___x_1041_ = lean_unsigned_to_nat(1u);
v___x_1042_ = lean_nat_add(v_snd_1040_, v___x_1041_);
lean_inc(v_a_1001_);
v___x_1043_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_j_1028_, v_snd_1040_, v_a_1001_);
v___x_1044_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1031_, v___x_1043_, v___x_1042_);
lean_dec(v___x_1043_);
v_fst_1045_ = lean_ctor_get(v___x_1044_, 0);
v_snd_1046_ = lean_ctor_get(v___x_1044_, 1);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1048_ = v___x_1044_;
v_isShared_1049_ = v_isSharedCheck_1059_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_snd_1046_);
lean_inc(v_fst_1045_);
lean_dec(v___x_1044_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1059_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
size_t v_sz_1050_; size_t v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1054_; 
v_sz_1050_ = lean_array_size(v_xs_1029_);
v___x_1051_ = ((size_t)0ULL);
v___x_1052_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(v_fst_1036_, v_sz_1050_, v___x_1051_, v_xs_1029_);
lean_dec(v_fst_1036_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 3, v_fst_1045_);
lean_ctor_set(v___x_1033_, 2, v_fst_1039_);
lean_ctor_set(v___x_1033_, 1, v___x_1052_);
lean_ctor_set(v___x_1033_, 0, v_snd_1040_);
v___x_1054_ = v___x_1033_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_snd_1040_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v_fst_1039_);
lean_ctor_set(v_reuseFailAlloc_1058_, 3, v_fst_1045_);
v___x_1054_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1056_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1054_);
v___x_1056_ = v___x_1048_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_snd_1046_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
v___jp_1060_:
{
lean_object* v_fst_1062_; lean_object* v_snd_1063_; 
v_fst_1062_ = lean_ctor_get(v___y_1061_, 0);
lean_inc(v_fst_1062_);
v_snd_1063_ = lean_ctor_get(v___y_1061_, 1);
lean_inc(v_snd_1063_);
lean_dec_ref(v___y_1061_);
v_fst_1036_ = v_fst_1062_;
v_snd_1037_ = v_snd_1063_;
goto v___jp_1035_;
}
}
}
case 2:
{
lean_object* v_x_1075_; lean_object* v_i_1076_; lean_object* v_y_1077_; lean_object* v_b_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1097_; 
v_x_1075_ = lean_ctor_get(v_x_1000_, 0);
v_i_1076_ = lean_ctor_get(v_x_1000_, 1);
v_y_1077_ = lean_ctor_get(v_x_1000_, 2);
v_b_1078_ = lean_ctor_get(v_x_1000_, 3);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_x_1000_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1080_ = v_x_1000_;
v_isShared_1081_ = v_isSharedCheck_1097_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_b_1078_);
lean_inc(v_y_1077_);
lean_inc(v_i_1076_);
lean_inc(v_x_1075_);
lean_dec(v_x_1000_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1097_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v_fst_1085_; lean_object* v_snd_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1096_; 
v___x_1082_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1075_, v_a_1001_);
lean_dec(v_x_1075_);
v___x_1083_ = l_Lean_IR_NormalizeIds_normArg(v_y_1077_, v_a_1001_);
v___x_1084_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1078_, v_a_1001_, v_a_1002_);
v_fst_1085_ = lean_ctor_get(v___x_1084_, 0);
v_snd_1086_ = lean_ctor_get(v___x_1084_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1088_ = v___x_1084_;
v_isShared_1089_ = v_isSharedCheck_1096_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_snd_1086_);
lean_inc(v_fst_1085_);
lean_dec(v___x_1084_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1096_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 3, v_fst_1085_);
lean_ctor_set(v___x_1080_, 2, v___x_1083_);
lean_ctor_set(v___x_1080_, 0, v___x_1082_);
v___x_1091_ = v___x_1080_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_i_1076_);
lean_ctor_set(v_reuseFailAlloc_1095_, 2, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1095_, 3, v_fst_1085_);
v___x_1091_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1093_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1091_);
v___x_1093_ = v___x_1088_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_snd_1086_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
case 3:
{
lean_object* v_x_1098_; lean_object* v_cidx_1099_; lean_object* v_b_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1118_; 
v_x_1098_ = lean_ctor_get(v_x_1000_, 0);
v_cidx_1099_ = lean_ctor_get(v_x_1000_, 1);
v_b_1100_ = lean_ctor_get(v_x_1000_, 2);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_x_1000_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1102_ = v_x_1000_;
v_isShared_1103_ = v_isSharedCheck_1118_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_b_1100_);
lean_inc(v_cidx_1099_);
lean_inc(v_x_1098_);
lean_dec(v_x_1000_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1118_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v_fst_1106_; lean_object* v_snd_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1117_; 
v___x_1104_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1098_, v_a_1001_);
lean_dec(v_x_1098_);
v___x_1105_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1100_, v_a_1001_, v_a_1002_);
v_fst_1106_ = lean_ctor_get(v___x_1105_, 0);
v_snd_1107_ = lean_ctor_get(v___x_1105_, 1);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1109_ = v___x_1105_;
v_isShared_1110_ = v_isSharedCheck_1117_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_snd_1107_);
lean_inc(v_fst_1106_);
lean_dec(v___x_1105_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1117_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 2, v_fst_1106_);
lean_ctor_set(v___x_1102_, 0, v___x_1104_);
v___x_1112_ = v___x_1102_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_cidx_1099_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v_fst_1106_);
v___x_1112_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1114_; 
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1112_);
v___x_1114_ = v___x_1109_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_snd_1107_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
case 4:
{
lean_object* v_x_1119_; lean_object* v_i_1120_; lean_object* v_y_1121_; lean_object* v_b_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1141_; 
v_x_1119_ = lean_ctor_get(v_x_1000_, 0);
v_i_1120_ = lean_ctor_get(v_x_1000_, 1);
v_y_1121_ = lean_ctor_get(v_x_1000_, 2);
v_b_1122_ = lean_ctor_get(v_x_1000_, 3);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_x_1000_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1124_ = v_x_1000_;
v_isShared_1125_ = v_isSharedCheck_1141_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_b_1122_);
lean_inc(v_y_1121_);
lean_inc(v_i_1120_);
lean_inc(v_x_1119_);
lean_dec(v_x_1000_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1141_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v_fst_1129_; lean_object* v_snd_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1140_; 
v___x_1126_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1119_, v_a_1001_);
lean_dec(v_x_1119_);
v___x_1127_ = l_Lean_IR_NormalizeIds_normIndex(v_y_1121_, v_a_1001_);
lean_dec(v_y_1121_);
v___x_1128_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1122_, v_a_1001_, v_a_1002_);
v_fst_1129_ = lean_ctor_get(v___x_1128_, 0);
v_snd_1130_ = lean_ctor_get(v___x_1128_, 1);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1132_ = v___x_1128_;
v_isShared_1133_ = v_isSharedCheck_1140_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_snd_1130_);
lean_inc(v_fst_1129_);
lean_dec(v___x_1128_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1140_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 3, v_fst_1129_);
lean_ctor_set(v___x_1124_, 2, v___x_1127_);
lean_ctor_set(v___x_1124_, 0, v___x_1126_);
v___x_1135_ = v___x_1124_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1126_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_i_1120_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1139_, 3, v_fst_1129_);
v___x_1135_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1137_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1135_);
v___x_1137_ = v___x_1132_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_snd_1130_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
case 5:
{
lean_object* v_x_1142_; lean_object* v_i_1143_; lean_object* v_offset_1144_; lean_object* v_y_1145_; lean_object* v_ty_1146_; lean_object* v_b_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1166_; 
v_x_1142_ = lean_ctor_get(v_x_1000_, 0);
v_i_1143_ = lean_ctor_get(v_x_1000_, 1);
v_offset_1144_ = lean_ctor_get(v_x_1000_, 2);
v_y_1145_ = lean_ctor_get(v_x_1000_, 3);
v_ty_1146_ = lean_ctor_get(v_x_1000_, 4);
v_b_1147_ = lean_ctor_get(v_x_1000_, 5);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_x_1000_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1149_ = v_x_1000_;
v_isShared_1150_ = v_isSharedCheck_1166_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_b_1147_);
lean_inc(v_ty_1146_);
lean_inc(v_y_1145_);
lean_inc(v_offset_1144_);
lean_inc(v_i_1143_);
lean_inc(v_x_1142_);
lean_dec(v_x_1000_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1166_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v_fst_1154_; lean_object* v_snd_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1165_; 
v___x_1151_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1142_, v_a_1001_);
lean_dec(v_x_1142_);
v___x_1152_ = l_Lean_IR_NormalizeIds_normIndex(v_y_1145_, v_a_1001_);
lean_dec(v_y_1145_);
v___x_1153_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1147_, v_a_1001_, v_a_1002_);
v_fst_1154_ = lean_ctor_get(v___x_1153_, 0);
v_snd_1155_ = lean_ctor_get(v___x_1153_, 1);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1157_ = v___x_1153_;
v_isShared_1158_ = v_isSharedCheck_1165_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_snd_1155_);
lean_inc(v_fst_1154_);
lean_dec(v___x_1153_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1165_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 5, v_fst_1154_);
lean_ctor_set(v___x_1149_, 3, v___x_1152_);
lean_ctor_set(v___x_1149_, 0, v___x_1151_);
v___x_1160_ = v___x_1149_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_i_1143_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_offset_1144_);
lean_ctor_set(v_reuseFailAlloc_1164_, 3, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1164_, 4, v_ty_1146_);
lean_ctor_set(v_reuseFailAlloc_1164_, 5, v_fst_1154_);
v___x_1160_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1162_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1160_);
v___x_1162_ = v___x_1157_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_snd_1155_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
case 6:
{
lean_object* v_x_1167_; lean_object* v_n_1168_; uint8_t v_c_1169_; uint8_t v_persistent_1170_; lean_object* v_b_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1189_; 
v_x_1167_ = lean_ctor_get(v_x_1000_, 0);
v_n_1168_ = lean_ctor_get(v_x_1000_, 1);
v_c_1169_ = lean_ctor_get_uint8(v_x_1000_, sizeof(void*)*3);
v_persistent_1170_ = lean_ctor_get_uint8(v_x_1000_, sizeof(void*)*3 + 1);
v_b_1171_ = lean_ctor_get(v_x_1000_, 2);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_x_1000_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1173_ = v_x_1000_;
v_isShared_1174_ = v_isSharedCheck_1189_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_b_1171_);
lean_inc(v_n_1168_);
lean_inc(v_x_1167_);
lean_dec(v_x_1000_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1189_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v_fst_1177_; lean_object* v_snd_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1188_; 
v___x_1175_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1167_, v_a_1001_);
lean_dec(v_x_1167_);
v___x_1176_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1171_, v_a_1001_, v_a_1002_);
v_fst_1177_ = lean_ctor_get(v___x_1176_, 0);
v_snd_1178_ = lean_ctor_get(v___x_1176_, 1);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1180_ = v___x_1176_;
v_isShared_1181_ = v_isSharedCheck_1188_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_snd_1178_);
lean_inc(v_fst_1177_);
lean_dec(v___x_1176_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1188_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 2, v_fst_1177_);
lean_ctor_set(v___x_1173_, 0, v___x_1175_);
v___x_1183_ = v___x_1173_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_n_1168_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v_fst_1177_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, sizeof(void*)*3, v_c_1169_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, sizeof(void*)*3 + 1, v_persistent_1170_);
v___x_1183_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1185_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v___x_1183_);
v___x_1185_ = v___x_1180_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_snd_1178_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
case 7:
{
lean_object* v_x_1190_; lean_object* v_n_1191_; uint8_t v_c_1192_; uint8_t v_persistent_1193_; lean_object* v_b_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1212_; 
v_x_1190_ = lean_ctor_get(v_x_1000_, 0);
v_n_1191_ = lean_ctor_get(v_x_1000_, 1);
v_c_1192_ = lean_ctor_get_uint8(v_x_1000_, sizeof(void*)*3);
v_persistent_1193_ = lean_ctor_get_uint8(v_x_1000_, sizeof(void*)*3 + 1);
v_b_1194_ = lean_ctor_get(v_x_1000_, 2);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_x_1000_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1196_ = v_x_1000_;
v_isShared_1197_ = v_isSharedCheck_1212_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_b_1194_);
lean_inc(v_n_1191_);
lean_inc(v_x_1190_);
lean_dec(v_x_1000_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1212_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v_fst_1200_; lean_object* v_snd_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1211_; 
v___x_1198_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1190_, v_a_1001_);
lean_dec(v_x_1190_);
v___x_1199_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1194_, v_a_1001_, v_a_1002_);
v_fst_1200_ = lean_ctor_get(v___x_1199_, 0);
v_snd_1201_ = lean_ctor_get(v___x_1199_, 1);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1203_ = v___x_1199_;
v_isShared_1204_ = v_isSharedCheck_1211_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_snd_1201_);
lean_inc(v_fst_1200_);
lean_dec(v___x_1199_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1211_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 2, v_fst_1200_);
lean_ctor_set(v___x_1196_, 0, v___x_1198_);
v___x_1206_ = v___x_1196_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_n_1191_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v_fst_1200_);
lean_ctor_set_uint8(v_reuseFailAlloc_1210_, sizeof(void*)*3, v_c_1192_);
lean_ctor_set_uint8(v_reuseFailAlloc_1210_, sizeof(void*)*3 + 1, v_persistent_1193_);
v___x_1206_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1208_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1206_);
v___x_1208_ = v___x_1203_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_snd_1201_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
case 8:
{
lean_object* v_x_1213_; lean_object* v_b_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1232_; 
v_x_1213_ = lean_ctor_get(v_x_1000_, 0);
v_b_1214_ = lean_ctor_get(v_x_1000_, 1);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_x_1000_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1216_ = v_x_1000_;
v_isShared_1217_ = v_isSharedCheck_1232_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_b_1214_);
lean_inc(v_x_1213_);
lean_dec(v_x_1000_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1232_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v_fst_1220_; lean_object* v_snd_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1231_; 
v___x_1218_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1213_, v_a_1001_);
lean_dec(v_x_1213_);
v___x_1219_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1214_, v_a_1001_, v_a_1002_);
v_fst_1220_ = lean_ctor_get(v___x_1219_, 0);
v_snd_1221_ = lean_ctor_get(v___x_1219_, 1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1223_ = v___x_1219_;
v_isShared_1224_ = v_isSharedCheck_1231_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_snd_1221_);
lean_inc(v_fst_1220_);
lean_dec(v___x_1219_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1231_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 1, v_fst_1220_);
lean_ctor_set(v___x_1216_, 0, v___x_1218_);
v___x_1226_ = v___x_1216_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_fst_1220_);
v___x_1226_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1228_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1226_);
v___x_1228_ = v___x_1223_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_snd_1221_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
case 9:
{
lean_object* v_tid_1233_; lean_object* v_x_1234_; lean_object* v_xType_1235_; lean_object* v_cs_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1256_; 
v_tid_1233_ = lean_ctor_get(v_x_1000_, 0);
v_x_1234_ = lean_ctor_get(v_x_1000_, 1);
v_xType_1235_ = lean_ctor_get(v_x_1000_, 2);
v_cs_1236_ = lean_ctor_get(v_x_1000_, 3);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_x_1000_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1238_ = v_x_1000_;
v_isShared_1239_ = v_isSharedCheck_1256_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_cs_1236_);
lean_inc(v_xType_1235_);
lean_inc(v_x_1234_);
lean_inc(v_tid_1233_);
lean_dec(v_x_1000_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1256_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; size_t v_sz_1241_; size_t v___x_1242_; lean_object* v___x_1243_; lean_object* v_fst_1244_; lean_object* v_snd_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1255_; 
v___x_1240_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1234_, v_a_1001_);
lean_dec(v_x_1234_);
v_sz_1241_ = lean_array_size(v_cs_1236_);
v___x_1242_ = ((size_t)0ULL);
v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(v_sz_1241_, v___x_1242_, v_cs_1236_, v_a_1001_, v_a_1002_);
v_fst_1244_ = lean_ctor_get(v___x_1243_, 0);
v_snd_1245_ = lean_ctor_get(v___x_1243_, 1);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1247_ = v___x_1243_;
v_isShared_1248_ = v_isSharedCheck_1255_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_snd_1245_);
lean_inc(v_fst_1244_);
lean_dec(v___x_1243_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1255_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 3, v_fst_1244_);
lean_ctor_set(v___x_1238_, 1, v___x_1240_);
v___x_1250_ = v___x_1238_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_tid_1233_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v_xType_1235_);
lean_ctor_set(v_reuseFailAlloc_1254_, 3, v_fst_1244_);
v___x_1250_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1252_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1250_);
v___x_1252_ = v___x_1247_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_snd_1245_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
}
case 10:
{
lean_object* v_x_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1266_; 
v_x_1257_ = lean_ctor_get(v_x_1000_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_x_1000_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1259_ = v_x_1000_;
v_isShared_1260_ = v_isSharedCheck_1266_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_x_1257_);
lean_dec(v_x_1000_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1266_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1261_ = l_Lean_IR_NormalizeIds_normArg(v_x_1257_, v_a_1001_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1261_);
v___x_1263_ = v___x_1259_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
lean_ctor_set(v___x_1264_, 1, v_a_1002_);
return v___x_1264_;
}
}
}
case 11:
{
lean_object* v_j_1267_; lean_object* v_ys_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1278_; 
v_j_1267_ = lean_ctor_get(v_x_1000_, 0);
v_ys_1268_ = lean_ctor_get(v_x_1000_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_x_1000_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1270_ = v_x_1000_;
v_isShared_1271_ = v_isSharedCheck_1278_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_ys_1268_);
lean_inc(v_j_1267_);
lean_dec(v_x_1000_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1278_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1272_ = l_Lean_IR_NormalizeIds_normIndex(v_j_1267_, v_a_1001_);
lean_dec(v_j_1267_);
v___x_1273_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_1268_, v_a_1001_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 1, v___x_1273_);
lean_ctor_set(v___x_1270_, 0, v___x_1272_);
v___x_1275_ = v___x_1270_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set(v___x_1276_, 1, v_a_1002_);
return v___x_1276_;
}
}
}
default: 
{
lean_object* v___x_1279_; 
v___x_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1279_, 0, v_x_1000_);
lean_ctor_set(v___x_1279_, 1, v_a_1002_);
return v___x_1279_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(size_t v_sz_1280_, size_t v_i_1281_, lean_object* v_bs_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
uint8_t v___x_1285_; 
v___x_1285_ = lean_usize_dec_lt(v_i_1281_, v_sz_1280_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1286_, 0, v_bs_1282_);
lean_ctor_set(v___x_1286_, 1, v___y_1284_);
return v___x_1286_;
}
else
{
lean_object* v_v_1287_; lean_object* v___x_1288_; lean_object* v_bs_x27_1289_; lean_object* v_fst_1291_; lean_object* v_snd_1292_; 
v_v_1287_ = lean_array_uget(v_bs_1282_, v_i_1281_);
v___x_1288_ = lean_unsigned_to_nat(0u);
v_bs_x27_1289_ = lean_array_uset(v_bs_1282_, v_i_1281_, v___x_1288_);
if (lean_obj_tag(v_v_1287_) == 0)
{
lean_object* v_info_1297_; lean_object* v_b_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1308_; 
v_info_1297_ = lean_ctor_get(v_v_1287_, 0);
v_b_1298_ = lean_ctor_get(v_v_1287_, 1);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_v_1287_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1300_ = v_v_1287_;
v_isShared_1301_ = v_isSharedCheck_1308_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_b_1298_);
lean_inc(v_info_1297_);
lean_dec(v_v_1287_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1308_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; lean_object* v_fst_1303_; lean_object* v_snd_1304_; lean_object* v___x_1306_; 
v___x_1302_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1298_, v___y_1283_, v___y_1284_);
v_fst_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_fst_1303_);
v_snd_1304_ = lean_ctor_get(v___x_1302_, 1);
lean_inc(v_snd_1304_);
lean_dec_ref(v___x_1302_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 1, v_fst_1303_);
v___x_1306_ = v___x_1300_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_info_1297_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_fst_1303_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
v_fst_1291_ = v___x_1306_;
v_snd_1292_ = v_snd_1304_;
goto v___jp_1290_;
}
}
}
else
{
lean_object* v_b_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1319_; 
v_b_1309_ = lean_ctor_get(v_v_1287_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_v_1287_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1311_ = v_v_1287_;
v_isShared_1312_ = v_isSharedCheck_1319_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_b_1309_);
lean_dec(v_v_1287_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1319_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v_fst_1314_; lean_object* v_snd_1315_; lean_object* v___x_1317_; 
v___x_1313_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1309_, v___y_1283_, v___y_1284_);
v_fst_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_fst_1314_);
v_snd_1315_ = lean_ctor_get(v___x_1313_, 1);
lean_inc(v_snd_1315_);
lean_dec_ref(v___x_1313_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v_fst_1314_);
v___x_1317_ = v___x_1311_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_fst_1314_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
v_fst_1291_ = v___x_1317_;
v_snd_1292_ = v_snd_1315_;
goto v___jp_1290_;
}
}
}
v___jp_1290_:
{
size_t v___x_1293_; size_t v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = ((size_t)1ULL);
v___x_1294_ = lean_usize_add(v_i_1281_, v___x_1293_);
v___x_1295_ = lean_array_uset(v_bs_x27_1289_, v_i_1281_, v_fst_1291_);
v_i_1281_ = v___x_1294_;
v_bs_1282_ = v___x_1295_;
v___y_1284_ = v_snd_1292_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2___boxed(lean_object* v_sz_1320_, lean_object* v_i_1321_, lean_object* v_bs_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
size_t v_sz_boxed_1325_; size_t v_i_boxed_1326_; lean_object* v_res_1327_; 
v_sz_boxed_1325_ = lean_unbox_usize(v_sz_1320_);
lean_dec(v_sz_1320_);
v_i_boxed_1326_ = lean_unbox_usize(v_i_1321_);
lean_dec(v_i_1321_);
v_res_1327_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(v_sz_boxed_1325_, v_i_boxed_1326_, v_bs_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___y_1323_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normFnBody___boxed(lean_object* v_x_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_IR_NormalizeIds_normFnBody(v_x_1328_, v_a_1329_, v_a_1330_);
lean_dec(v_a_1329_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normDecl(lean_object* v_d_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
if (lean_obj_tag(v_d_1332_) == 0)
{
lean_object* v_xs_1335_; lean_object* v_body_1336_; lean_object* v_fst_1338_; lean_object* v_snd_1339_; lean_object* v___y_1352_; lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v_xs_1335_ = lean_ctor_get(v_d_1332_, 1);
v_body_1336_ = lean_ctor_get(v_d_1332_, 3);
v___x_1355_ = lean_unsigned_to_nat(0u);
v___x_1356_ = lean_array_get_size(v_xs_1335_);
v___x_1357_ = lean_nat_dec_lt(v___x_1355_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_inc(v_a_1333_);
v_fst_1338_ = v_a_1333_;
v_snd_1339_ = v_a_1334_;
goto v___jp_1337_;
}
else
{
uint8_t v___x_1358_; 
v___x_1358_ = lean_nat_dec_le(v___x_1356_, v___x_1356_);
if (v___x_1358_ == 0)
{
if (v___x_1357_ == 0)
{
lean_inc(v_a_1333_);
v_fst_1338_ = v_a_1333_;
v_snd_1339_ = v_a_1334_;
goto v___jp_1337_;
}
else
{
size_t v___x_1359_; size_t v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = ((size_t)0ULL);
v___x_1360_ = lean_usize_of_nat(v___x_1356_);
lean_inc(v_a_1333_);
v___x_1361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_1335_, v___x_1359_, v___x_1360_, v_a_1333_, v_a_1334_);
v___y_1352_ = v___x_1361_;
goto v___jp_1351_;
}
}
else
{
size_t v___x_1362_; size_t v___x_1363_; lean_object* v___x_1364_; 
v___x_1362_ = ((size_t)0ULL);
v___x_1363_ = lean_usize_of_nat(v___x_1356_);
lean_inc(v_a_1333_);
v___x_1364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_1335_, v___x_1362_, v___x_1363_, v_a_1333_, v_a_1334_);
v___y_1352_ = v___x_1364_;
goto v___jp_1351_;
}
}
v___jp_1337_:
{
lean_object* v___x_1340_; lean_object* v_fst_1341_; lean_object* v_snd_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1350_; 
lean_inc(v_body_1336_);
v___x_1340_ = l_Lean_IR_NormalizeIds_normFnBody(v_body_1336_, v_fst_1338_, v_snd_1339_);
lean_dec(v_fst_1338_);
v_fst_1341_ = lean_ctor_get(v___x_1340_, 0);
v_snd_1342_ = lean_ctor_get(v___x_1340_, 1);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1344_ = v___x_1340_;
v_isShared_1345_ = v_isSharedCheck_1350_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_snd_1342_);
lean_inc(v_fst_1341_);
lean_dec(v___x_1340_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1350_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1346_ = l_Lean_IR_Decl_updateBody_x21(v_d_1332_, v_fst_1341_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1346_);
v___x_1348_ = v___x_1344_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_snd_1342_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
v___jp_1351_:
{
lean_object* v_fst_1353_; lean_object* v_snd_1354_; 
v_fst_1353_ = lean_ctor_get(v___y_1352_, 0);
lean_inc(v_fst_1353_);
v_snd_1354_ = lean_ctor_get(v___y_1352_, 1);
lean_inc(v_snd_1354_);
lean_dec_ref(v___y_1352_);
v_fst_1338_ = v_fst_1353_;
v_snd_1339_ = v_snd_1354_;
goto v___jp_1337_;
}
}
else
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v_d_1332_);
lean_ctor_set(v___x_1365_, 1, v_a_1334_);
return v___x_1365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normDecl___boxed(lean_object* v_d_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_IR_NormalizeIds_normDecl(v_d_1366_, v_a_1367_, v_a_1368_);
lean_dec(v_a_1367_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_normalizeIds(lean_object* v_d_1370_){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v_fst_1374_; 
v___x_1371_ = lean_box(1);
v___x_1372_ = lean_unsigned_to_nat(1u);
v___x_1373_ = l_Lean_IR_NormalizeIds_normDecl(v_d_1370_, v___x_1371_, v___x_1372_);
v_fst_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_fst_1374_);
lean_dec_ref(v___x_1373_);
return v_fst_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArg(lean_object* v_f_1375_, lean_object* v_x_1376_){
_start:
{
if (lean_obj_tag(v_x_1376_) == 0)
{
lean_object* v_id_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1385_; 
v_id_1377_ = lean_ctor_get(v_x_1376_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_x_1376_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1379_ = v_x_1376_;
v_isShared_1380_ = v_isSharedCheck_1385_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_id_1377_);
lean_dec(v_x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1385_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v___x_1383_; 
v___x_1381_ = lean_apply_1(v_f_1375_, v_id_1377_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1381_);
v___x_1383_ = v___x_1379_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
else
{
lean_dec_ref(v_f_1375_);
return v_x_1376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(lean_object* v_f_1386_, size_t v_sz_1387_, size_t v_i_1388_, lean_object* v_bs_1389_){
_start:
{
uint8_t v___x_1390_; 
v___x_1390_ = lean_usize_dec_lt(v_i_1388_, v_sz_1387_);
if (v___x_1390_ == 0)
{
lean_dec_ref(v_f_1386_);
return v_bs_1389_;
}
else
{
lean_object* v_v_1391_; lean_object* v___x_1392_; lean_object* v_bs_x27_1393_; lean_object* v___y_1395_; 
v_v_1391_ = lean_array_uget(v_bs_1389_, v_i_1388_);
v___x_1392_ = lean_unsigned_to_nat(0u);
v_bs_x27_1393_ = lean_array_uset(v_bs_1389_, v_i_1388_, v___x_1392_);
if (lean_obj_tag(v_v_1391_) == 0)
{
lean_object* v_id_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1408_; 
v_id_1400_ = lean_ctor_get(v_v_1391_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_v_1391_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1402_ = v_v_1391_;
v_isShared_1403_ = v_isSharedCheck_1408_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_id_1400_);
lean_dec(v_v_1391_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1408_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1406_; 
lean_inc_ref(v_f_1386_);
v___x_1404_ = lean_apply_1(v_f_1386_, v_id_1400_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v___x_1404_);
v___x_1406_ = v___x_1402_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
v___y_1395_ = v___x_1406_;
goto v___jp_1394_;
}
}
}
else
{
v___y_1395_ = v_v_1391_;
goto v___jp_1394_;
}
v___jp_1394_:
{
size_t v___x_1396_; size_t v___x_1397_; lean_object* v___x_1398_; 
v___x_1396_ = ((size_t)1ULL);
v___x_1397_ = lean_usize_add(v_i_1388_, v___x_1396_);
v___x_1398_ = lean_array_uset(v_bs_x27_1393_, v_i_1388_, v___y_1395_);
v_i_1388_ = v___x_1397_;
v_bs_1389_ = v___x_1398_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0___boxed(lean_object* v_f_1409_, lean_object* v_sz_1410_, lean_object* v_i_1411_, lean_object* v_bs_1412_){
_start:
{
size_t v_sz_boxed_1413_; size_t v_i_boxed_1414_; lean_object* v_res_1415_; 
v_sz_boxed_1413_ = lean_unbox_usize(v_sz_1410_);
lean_dec(v_sz_1410_);
v_i_boxed_1414_ = lean_unbox_usize(v_i_1411_);
lean_dec(v_i_1411_);
v_res_1415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(v_f_1409_, v_sz_boxed_1413_, v_i_boxed_1414_, v_bs_1412_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArgs(lean_object* v_f_1416_, lean_object* v_as_1417_){
_start:
{
size_t v_sz_1418_; size_t v___x_1419_; lean_object* v___x_1420_; 
v_sz_1418_ = lean_array_size(v_as_1417_);
v___x_1419_ = ((size_t)0ULL);
v___x_1420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(v_f_1416_, v_sz_1418_, v___x_1419_, v_as_1417_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapExpr(lean_object* v_f_1421_, lean_object* v_x_1422_){
_start:
{
switch(lean_obj_tag(v_x_1422_))
{
case 0:
{
lean_object* v_i_1423_; lean_object* v_ys_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1432_; 
v_i_1423_ = lean_ctor_get(v_x_1422_, 0);
v_ys_1424_ = lean_ctor_get(v_x_1422_, 1);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_x_1422_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1426_ = v_x_1422_;
v_isShared_1427_ = v_isSharedCheck_1432_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_ys_1424_);
lean_inc(v_i_1423_);
lean_dec(v_x_1422_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1432_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1428_ = l_Lean_IR_MapVars_mapArgs(v_f_1421_, v_ys_1424_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 1, v___x_1428_);
v___x_1430_ = v___x_1426_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_i_1423_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
case 1:
{
lean_object* v_n_1433_; lean_object* v_x_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1442_; 
v_n_1433_ = lean_ctor_get(v_x_1422_, 0);
v_x_1434_ = lean_ctor_get(v_x_1422_, 1);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_x_1422_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1436_ = v_x_1422_;
v_isShared_1437_ = v_isSharedCheck_1442_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_x_1434_);
lean_inc(v_n_1433_);
lean_dec(v_x_1422_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1442_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1438_ = lean_apply_1(v_f_1421_, v_x_1434_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 1, v___x_1438_);
v___x_1440_ = v___x_1436_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_n_1433_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
case 2:
{
lean_object* v_x_1443_; lean_object* v_i_1444_; uint8_t v_updtHeader_1445_; lean_object* v_ys_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1455_; 
v_x_1443_ = lean_ctor_get(v_x_1422_, 0);
v_i_1444_ = lean_ctor_get(v_x_1422_, 1);
v_updtHeader_1445_ = lean_ctor_get_uint8(v_x_1422_, sizeof(void*)*3);
v_ys_1446_ = lean_ctor_get(v_x_1422_, 2);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_x_1422_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1448_ = v_x_1422_;
v_isShared_1449_ = v_isSharedCheck_1455_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_ys_1446_);
lean_inc(v_i_1444_);
lean_inc(v_x_1443_);
lean_dec(v_x_1422_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1455_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1453_; 
lean_inc_ref(v_f_1421_);
v___x_1450_ = lean_apply_1(v_f_1421_, v_x_1443_);
v___x_1451_ = l_Lean_IR_MapVars_mapArgs(v_f_1421_, v_ys_1446_);
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 2, v___x_1451_);
lean_ctor_set(v___x_1448_, 0, v___x_1450_);
v___x_1453_ = v___x_1448_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_i_1444_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v___x_1451_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*3, v_updtHeader_1445_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
case 3:
{
lean_object* v_i_1456_; lean_object* v_x_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1465_; 
v_i_1456_ = lean_ctor_get(v_x_1422_, 0);
v_x_1457_ = lean_ctor_get(v_x_1422_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_x_1422_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1459_ = v_x_1422_;
v_isShared_1460_ = v_isSharedCheck_1465_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_x_1457_);
lean_inc(v_i_1456_);
lean_dec(v_x_1422_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1465_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v___x_1463_; 
v___x_1461_ = lean_apply_1(v_f_1421_, v_x_1457_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 1, v___x_1461_);
v___x_1463_ = v___x_1459_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_i_1456_);
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
case 4:
{
lean_object* v_i_1466_; lean_object* v_x_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1475_; 
v_i_1466_ = lean_ctor_get(v_x_1422_, 0);
v_x_1467_ = lean_ctor_get(v_x_1422_, 1);
v_isSharedCheck_1475_ = !lean_is_exclusive(v_x_1422_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1469_ = v_x_1422_;
v_isShared_1470_ = v_isSharedCheck_1475_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_x_1467_);
lean_inc(v_i_1466_);
lean_dec(v_x_1422_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1475_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; lean_object* v___x_1473_; 
v___x_1471_ = lean_apply_1(v_f_1421_, v_x_1467_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 1, v___x_1471_);
v___x_1473_ = v___x_1469_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_i_1466_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
case 5:
{
lean_object* v_n_1476_; lean_object* v_offset_1477_; lean_object* v_x_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1486_; 
v_n_1476_ = lean_ctor_get(v_x_1422_, 0);
v_offset_1477_ = lean_ctor_get(v_x_1422_, 1);
v_x_1478_ = lean_ctor_get(v_x_1422_, 2);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_x_1422_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1480_ = v_x_1422_;
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_x_1478_);
lean_inc(v_offset_1477_);
lean_inc(v_n_1476_);
lean_dec(v_x_1422_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1482_ = lean_apply_1(v_f_1421_, v_x_1478_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 2, v___x_1482_);
v___x_1484_ = v___x_1480_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_n_1476_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_offset_1477_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
case 6:
{
lean_object* v_c_1487_; lean_object* v_ys_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1496_; 
v_c_1487_ = lean_ctor_get(v_x_1422_, 0);
v_ys_1488_ = lean_ctor_get(v_x_1422_, 1);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_x_1422_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1490_ = v_x_1422_;
v_isShared_1491_ = v_isSharedCheck_1496_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_ys_1488_);
lean_inc(v_c_1487_);
lean_dec(v_x_1422_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1496_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1492_ = l_Lean_IR_MapVars_mapArgs(v_f_1421_, v_ys_1488_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v___x_1492_);
v___x_1494_ = v___x_1490_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_c_1487_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
case 7:
{
lean_object* v_c_1497_; lean_object* v_ys_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1506_; 
v_c_1497_ = lean_ctor_get(v_x_1422_, 0);
v_ys_1498_ = lean_ctor_get(v_x_1422_, 1);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_x_1422_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1500_ = v_x_1422_;
v_isShared_1501_ = v_isSharedCheck_1506_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_ys_1498_);
lean_inc(v_c_1497_);
lean_dec(v_x_1422_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1506_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; lean_object* v___x_1504_; 
v___x_1502_ = l_Lean_IR_MapVars_mapArgs(v_f_1421_, v_ys_1498_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v___x_1502_);
v___x_1504_ = v___x_1500_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_c_1497_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
case 8:
{
lean_object* v_x_1507_; lean_object* v_ys_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1517_; 
v_x_1507_ = lean_ctor_get(v_x_1422_, 0);
v_ys_1508_ = lean_ctor_get(v_x_1422_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_x_1422_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1510_ = v_x_1422_;
v_isShared_1511_ = v_isSharedCheck_1517_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_ys_1508_);
lean_inc(v_x_1507_);
lean_dec(v_x_1422_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1517_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
lean_inc_ref(v_f_1421_);
v___x_1512_ = lean_apply_1(v_f_1421_, v_x_1507_);
v___x_1513_ = l_Lean_IR_MapVars_mapArgs(v_f_1421_, v_ys_1508_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 1, v___x_1513_);
lean_ctor_set(v___x_1510_, 0, v___x_1512_);
v___x_1515_ = v___x_1510_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
case 9:
{
lean_object* v_ty_1518_; lean_object* v_x_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1527_; 
v_ty_1518_ = lean_ctor_get(v_x_1422_, 0);
v_x_1519_ = lean_ctor_get(v_x_1422_, 1);
v_isSharedCheck_1527_ = !lean_is_exclusive(v_x_1422_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1521_ = v_x_1422_;
v_isShared_1522_ = v_isSharedCheck_1527_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_x_1519_);
lean_inc(v_ty_1518_);
lean_dec(v_x_1422_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1527_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1523_ = lean_apply_1(v_f_1421_, v_x_1519_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 1, v___x_1523_);
v___x_1525_ = v___x_1521_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_ty_1518_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
case 10:
{
lean_object* v_x_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1536_; 
v_x_1528_ = lean_ctor_get(v_x_1422_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_x_1422_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1530_ = v_x_1422_;
v_isShared_1531_ = v_isSharedCheck_1536_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_x_1528_);
lean_dec(v_x_1422_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1536_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1532_ = lean_apply_1(v_f_1421_, v_x_1528_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v___x_1532_);
v___x_1534_ = v___x_1530_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
case 11:
{
lean_dec_ref(v_f_1421_);
return v_x_1422_;
}
default: 
{
lean_object* v_x_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1545_; 
v_x_1537_ = lean_ctor_get(v_x_1422_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_x_1422_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1539_ = v_x_1422_;
v_isShared_1540_ = v_isSharedCheck_1545_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_x_1537_);
lean_dec(v_x_1422_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1545_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1541_ = lean_apply_1(v_f_1421_, v_x_1537_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1541_);
v___x_1543_ = v___x_1539_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapFnBody(lean_object* v_f_1546_, lean_object* v_x_1547_){
_start:
{
switch(lean_obj_tag(v_x_1547_))
{
case 0:
{
lean_object* v_x_1548_; lean_object* v_ty_1549_; lean_object* v_e_1550_; lean_object* v_b_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1560_; 
v_x_1548_ = lean_ctor_get(v_x_1547_, 0);
v_ty_1549_ = lean_ctor_get(v_x_1547_, 1);
v_e_1550_ = lean_ctor_get(v_x_1547_, 2);
v_b_1551_ = lean_ctor_get(v_x_1547_, 3);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_x_1547_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1553_ = v_x_1547_;
v_isShared_1554_ = v_isSharedCheck_1560_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_b_1551_);
lean_inc(v_e_1550_);
lean_inc(v_ty_1549_);
lean_inc(v_x_1548_);
lean_dec(v_x_1547_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1560_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1558_; 
lean_inc_ref(v_f_1546_);
v___x_1555_ = l_Lean_IR_MapVars_mapExpr(v_f_1546_, v_e_1550_);
v___x_1556_ = l_Lean_IR_MapVars_mapFnBody(v_f_1546_, v_b_1551_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 3, v___x_1556_);
lean_ctor_set(v___x_1553_, 2, v___x_1555_);
v___x_1558_ = v___x_1553_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_x_1548_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_ty_1549_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v___x_1555_);
lean_ctor_set(v_reuseFailAlloc_1559_, 3, v___x_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
case 1:
{
lean_object* v_j_1561_; lean_object* v_xs_1562_; lean_object* v_v_1563_; lean_object* v_b_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1573_; 
v_j_1561_ = lean_ctor_get(v_x_1547_, 0);
v_xs_1562_ = lean_ctor_get(v_x_1547_, 1);
v_v_1563_ = lean_ctor_get(v_x_1547_, 2);
v_b_1564_ = lean_ctor_get(v_x_1547_, 3);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_x_1547_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1566_ = v_x_1547_;
v_isShared_1567_ = v_isSharedCheck_1573_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_b_1564_);
lean_inc(v_v_1563_);
lean_inc(v_xs_1562_);
lean_inc(v_j_1561_);
lean_dec(v_x_1547_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1573_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
lean_inc_ref(v_f_1546_);
v___x_1568_ = l_Lean_IR_MapVars_mapFnBody(v_f_1546_, v_v_1563_);
v___x_1569_ = l_Lean_IR_MapVars_mapFnBody(v_f_1546_, v_b_1564_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 3, v___x_1569_);
lean_ctor_set(v___x_1566_, 2, v___x_1568_);
v___x_1571_ = v___x_1566_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_j_1561_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_xs_1562_);
lean_ctor_set(v_reuseFailAlloc_1572_, 2, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1572_, 3, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
case 2:
{
lean_object* v_x_1574_; lean_object* v_i_1575_; lean_object* v_y_1576_; lean_object* v_b_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1597_; 
v_x_1574_ = lean_ctor_get(v_x_1547_, 0);
v_i_1575_ = lean_ctor_get(v_x_1547_, 1);
v_y_1576_ = lean_ctor_get(v_x_1547_, 2);
v_b_1577_ = lean_ctor_get(v_x_1547_, 3);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_x_1547_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1579_ = v_x_1547_;
v_isShared_1580_ = v_isSharedCheck_1597_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_b_1577_);
lean_inc(v_y_1576_);
lean_inc(v_i_1575_);
lean_inc(v_x_1574_);
lean_dec(v_x_1547_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1597_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; lean_object* v___y_1583_; 
lean_inc_ref(v_f_1546_);
v___x_1581_ = lean_apply_1(v_f_1546_, v_x_1574_);
if (lean_obj_tag(v_y_1576_) == 0)
{
lean_object* v_id_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1596_; 
v_id_1588_ = lean_ctor_get(v_y_1576_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_y_1576_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1590_ = v_y_1576_;
v_isShared_1591_ = v_isSharedCheck_1596_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_id_1588_);
lean_dec(v_y_1576_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1596_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1592_; lean_object* v___x_1594_; 
lean_inc_ref(v_f_1546_);
v___x_1592_ = lean_apply_1(v_f_1546_, v_id_1588_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1592_);
v___x_1594_ = v___x_1590_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
v___y_1583_ = v___x_1594_;
goto v___jp_1582_;
}
}
}
else
{
v___y_1583_ = v_y_1576_;
goto v___jp_1582_;
}
v___jp_1582_:
{
lean_object* v___x_1584_; lean_object* v___x_1586_; 
v___x_1584_ = l_Lean_IR_MapVars_mapFnBody(v_f_1546_, v_b_1577_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 3, v___x_1584_);
lean_ctor_set(v___x_1579_, 2, v___y_1583_);
lean_ctor_set(v___x_1579_, 0, v___x_1581_);
v___x_1586_ = v___x_1579_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_i_1575_);
lean_ctor_set(v_reuseFailAlloc_1587_, 2, v___y_1583_);
lean_ctor_set(v_reuseFailAlloc_1587_, 3, v___x_1584_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
case 3:
{
lean_object* v_x_1598_; lean_object* v_cidx_1599_; lean_object* v_b_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1609_; 
v_x_1598_ = lean_ctor_get(v_x_1547_, 0);
v_cidx_1599_ = lean_ctor_get(v_x_1547_, 1);
v_b_1600_ = lean_ctor_get(v_x_1547_, 2);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_x_1547_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1602_ = v_x_1547_;
v_isShared_1603_ = v_isSharedCheck_1609_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_b_1600_);
lean_inc(v_cidx_1599_);
lean_inc(v_x_1598_);
lean_dec(v_x_1547_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1609_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1607_; 
lean_inc_ref(v_f_1546_);
v___x_1604_ = lean_apply_1(v_f_1546_, v_x_1598_);
v___x_1605_ = l_Lean_IR_MapVars_mapFnBody(v_f_1546_, v_b_1600_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 2, v___x_1605_);
lean_ctor_set(v___x_1602_, 0, v___x_1604_);
v___x_1607_ = v___x_1602_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_cidx_1599_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
case 4:
{
lean_object* v_x_1610_; lean_object* v_i_1611_; lean_object* v_y_1612_; lean_object* v_b_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1623_; 
v_x_1610_ = lean_ctor_get(v_x_1547_, 0);
v_i_1611_ = lean_ctor_get(v_x_1547_, 1);
v_y_1612_ = lean_ctor_get(v_x_1547_, 2);
v_b_1613_ = lean_ctor_get(v_x_1547_, 3);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_x_1547_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1615_ = v_x_1547_;
v_isShared_1616_ = v_isSharedCheck_1623_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_b_1613_);
lean_inc(v_y_1612_);
lean_inc(v_i_1611_);
lean_inc(v_x_1610_);
lean_dec(v_x_1547_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1623_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
lean_inc_ref_n(v_f_1546_, 2);
v___x_1617_ = lean_apply_1(v_f_1546_, v_x_1610_);
v___x_1618_ = lean_apply_1(v_f_1546_, v_y_1612_);
v___x_1619_ = l_Lean_IR_MapVars_mapFnBody(v_f_1546_, v_b_1613_);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 3, v___x_1619_);
lean_ctor_set(v___x_1615_, 2, v___x_1618_);
lean_ctor_set(v___x_1615_, 0, v___x_1617_);
v___x_1621_ = v___x_1615_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1617_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_i_1611_);
lean_ctor_set(v_reuseFailAlloc_1622_, 2, v___x_1618_);
lean_ctor_set(v_reuseFailAlloc_1622_, 3, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
case 5:
{
lean_object* v_x_1624_; lean_object* v_i_1625_; lean_object* v_offset_1626_; lean_object* v_y_1627_; lean_object* v_ty_1628_; lean_object* v_b_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1639_; 
v_x_1624_ = lean_ctor_get(v_x_1547_, 0);
v_i_1625_ = lean_ctor_get(v_x_1547_, 1);
v_offset_1626_ = lean_ctor_get(v_x_1547_, 2);
v_y_1627_ = lean_ctor_get(v_x_1547_, 3);
v_ty_1628_ = lean_ctor_get(v_x_1547_, 4);
v_b_1629_ = lean_ctor_get(v_x_1547_, 5);
v_isSharedCheck_1639_ = !lean_is_exclusive(v_x_1547_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1631_ = v_x_1547_;
v_isShared_1632_ = v_isSharedCheck_1639_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_b_1629_);
lean_inc(v_ty_1628_);
lean_inc(v_y_1627_);
lean_inc(v_offset_1626_);
lean_inc(v_i_1625_);
lean_inc(v_x_1624_);
lean_dec(v_x_1547_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1639_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1637_; 
lean_inc_ref_n(v_f_1546_, 2);
v___x_1633_ = lean_apply_1(v_f_1546_, v_x_1624_);
v___x_1634_ = lean_apply_1(v_f_1546_, v_y_1627_);
v___x_1635_ = l_Lean_IR_MapVars_mapFnBody(v_f_1546_, v_b_1629_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 5, v___x_1635_);
lean_ctor_set(v___x_1631_, 3, v___x_1634_);
lean_ctor_set(v___x_1631_, 0, v___x_1633_);
v___x_1637_ = v___x_1631_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_i_1625_);
lean_ctor_set(v_reuseFailAlloc_1638_, 2, v_offset_1626_);
lean_ctor_set(v_reuseFailAlloc_1638_, 3, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1638_, 4, v_ty_1628_);
lean_ctor_set(v_reuseFailAlloc_1638_, 5, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
case 6:
{
lean_object* v_x_1640_; lean_object* v_n_1641_; uint8_t v_c_1642_; uint8_t v_persistent_1643_; lean_object* v_b_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1653_; 
v_x_1640_ = lean_ctor_get(v_x_1547_, 0);
v_n_1641_ = lean_ctor_get(v_x_1547_, 1);
v_c_1642_ = lean_ctor_get_uint8(v_x_1547_, sizeof(void*)*3);
v_persistent_1643_ = lean_ctor_get_uint8(v_x_1547_, sizeof(void*)*3 + 1);
v_b_1644_ = lean_ctor_get(v_x_1547_, 2);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_x_1547_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1646_ = v_x_1547_;
v_isShared_1647_ = v_isSharedCheck_1653_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_b_1644_);
lean_inc(v_n_1641_);
lean_inc(v_x_1640_);
lean_dec(v_x_1547_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1653_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1651_; 
lean_inc_ref(v_f_1546_);
v___x_1648_ = lean_apply_1(v_f_1546_, v_x_1640_);
v___x_1649_ = l_Lean_IR_MapVars_mapFnBody(v_f_1546_, v_b_1644_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 2, v___x_1649_);
lean_ctor_set(v___x_1646_, 0, v___x_1648_);
v___x_1651_ = v___x_1646_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_n_1641_);
lean_ctor_set(v_reuseFailAlloc_1652_, 2, v___x_1649_);
lean_ctor_set_uint8(v_reuseFailAlloc_1652_, sizeof(void*)*3, v_c_1642_);
lean_ctor_set_uint8(v_reuseFailAlloc_1652_, sizeof(void*)*3 + 1, v_persistent_1643_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
case 7:
{
lean_object* v_x_1654_; lean_object* v_n_1655_; uint8_t v_c_1656_; uint8_t v_persistent_1657_; lean_object* v_b_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1667_; 
v_x_1654_ = lean_ctor_get(v_x_1547_, 0);
v_n_1655_ = lean_ctor_get(v_x_1547_, 1);
v_c_1656_ = lean_ctor_get_uint8(v_x_1547_, sizeof(void*)*3);
v_persistent_1657_ = lean_ctor_get_uint8(v_x_1547_, sizeof(void*)*3 + 1);
v_b_1658_ = lean_ctor_get(v_x_1547_, 2);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_x_1547_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1660_ = v_x_1547_;
v_isShared_1661_ = v_isSharedCheck_1667_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_b_1658_);
lean_inc(v_n_1655_);
lean_inc(v_x_1654_);
lean_dec(v_x_1547_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1667_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1665_; 
lean_inc_ref(v_f_1546_);
v___x_1662_ = lean_apply_1(v_f_1546_, v_x_1654_);
v___x_1663_ = l_Lean_IR_MapVars_mapFnBody(v_f_1546_, v_b_1658_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 2, v___x_1663_);
lean_ctor_set(v___x_1660_, 0, v___x_1662_);
v___x_1665_ = v___x_1660_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_n_1655_);
lean_ctor_set(v_reuseFailAlloc_1666_, 2, v___x_1663_);
lean_ctor_set_uint8(v_reuseFailAlloc_1666_, sizeof(void*)*3, v_c_1656_);
lean_ctor_set_uint8(v_reuseFailAlloc_1666_, sizeof(void*)*3 + 1, v_persistent_1657_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
case 8:
{
lean_object* v_x_1668_; lean_object* v_b_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1678_; 
v_x_1668_ = lean_ctor_get(v_x_1547_, 0);
v_b_1669_ = lean_ctor_get(v_x_1547_, 1);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_x_1547_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1671_ = v_x_1547_;
v_isShared_1672_ = v_isSharedCheck_1678_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_b_1669_);
lean_inc(v_x_1668_);
lean_dec(v_x_1547_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1678_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1676_; 
lean_inc_ref(v_f_1546_);
v___x_1673_ = lean_apply_1(v_f_1546_, v_x_1668_);
v___x_1674_ = l_Lean_IR_MapVars_mapFnBody(v_f_1546_, v_b_1669_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 1, v___x_1674_);
lean_ctor_set(v___x_1671_, 0, v___x_1673_);
v___x_1676_ = v___x_1671_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
case 9:
{
lean_object* v_tid_1679_; lean_object* v_x_1680_; lean_object* v_xType_1681_; lean_object* v_cs_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1693_; 
v_tid_1679_ = lean_ctor_get(v_x_1547_, 0);
v_x_1680_ = lean_ctor_get(v_x_1547_, 1);
v_xType_1681_ = lean_ctor_get(v_x_1547_, 2);
v_cs_1682_ = lean_ctor_get(v_x_1547_, 3);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_x_1547_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1684_ = v_x_1547_;
v_isShared_1685_ = v_isSharedCheck_1693_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_cs_1682_);
lean_inc(v_xType_1681_);
lean_inc(v_x_1680_);
lean_inc(v_tid_1679_);
lean_dec(v_x_1547_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1693_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; size_t v_sz_1687_; size_t v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
lean_inc_ref(v_f_1546_);
v___x_1686_ = lean_apply_1(v_f_1546_, v_x_1680_);
v_sz_1687_ = lean_array_size(v_cs_1682_);
v___x_1688_ = ((size_t)0ULL);
v___x_1689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(v_f_1546_, v_sz_1687_, v___x_1688_, v_cs_1682_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 3, v___x_1689_);
lean_ctor_set(v___x_1684_, 1, v___x_1686_);
v___x_1691_ = v___x_1684_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_tid_1679_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v___x_1686_);
lean_ctor_set(v_reuseFailAlloc_1692_, 2, v_xType_1681_);
lean_ctor_set(v_reuseFailAlloc_1692_, 3, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
case 10:
{
lean_object* v_x_1694_; 
v_x_1694_ = lean_ctor_get(v_x_1547_, 0);
lean_inc(v_x_1694_);
if (lean_obj_tag(v_x_1694_) == 0)
{
lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1710_; 
v_isSharedCheck_1710_ = !lean_is_exclusive(v_x_1547_);
if (v_isSharedCheck_1710_ == 0)
{
lean_object* v_unused_1711_; 
v_unused_1711_ = lean_ctor_get(v_x_1547_, 0);
lean_dec(v_unused_1711_);
v___x_1696_ = v_x_1547_;
v_isShared_1697_ = v_isSharedCheck_1710_;
goto v_resetjp_1695_;
}
else
{
lean_dec(v_x_1547_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1710_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v_id_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1709_; 
v_id_1698_ = lean_ctor_get(v_x_1694_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_x_1694_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1700_ = v_x_1694_;
v_isShared_1701_ = v_isSharedCheck_1709_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_id_1698_);
lean_dec(v_x_1694_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1709_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1702_ = lean_apply_1(v_f_1546_, v_id_1698_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1702_);
v___x_1704_ = v___x_1700_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1706_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1704_);
v___x_1706_ = v___x_1696_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_1546_);
return v_x_1547_;
}
}
case 11:
{
lean_object* v_j_1712_; lean_object* v_ys_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1721_; 
v_j_1712_ = lean_ctor_get(v_x_1547_, 0);
v_ys_1713_ = lean_ctor_get(v_x_1547_, 1);
v_isSharedCheck_1721_ = !lean_is_exclusive(v_x_1547_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1715_ = v_x_1547_;
v_isShared_1716_ = v_isSharedCheck_1721_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_ys_1713_);
lean_inc(v_j_1712_);
lean_dec(v_x_1547_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1721_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1717_ = l_Lean_IR_MapVars_mapArgs(v_f_1546_, v_ys_1713_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v___x_1717_);
v___x_1719_ = v___x_1715_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_j_1712_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
default: 
{
lean_dec_ref(v_f_1546_);
return v_x_1547_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(lean_object* v_f_1722_, size_t v_sz_1723_, size_t v_i_1724_, lean_object* v_bs_1725_){
_start:
{
uint8_t v___x_1726_; 
v___x_1726_ = lean_usize_dec_lt(v_i_1724_, v_sz_1723_);
if (v___x_1726_ == 0)
{
lean_dec_ref(v_f_1722_);
return v_bs_1725_;
}
else
{
lean_object* v_v_1727_; lean_object* v___x_1728_; lean_object* v_bs_x27_1729_; lean_object* v___y_1731_; 
v_v_1727_ = lean_array_uget(v_bs_1725_, v_i_1724_);
v___x_1728_ = lean_unsigned_to_nat(0u);
v_bs_x27_1729_ = lean_array_uset(v_bs_1725_, v_i_1724_, v___x_1728_);
if (lean_obj_tag(v_v_1727_) == 0)
{
lean_object* v_info_1736_; lean_object* v_b_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1745_; 
v_info_1736_ = lean_ctor_get(v_v_1727_, 0);
v_b_1737_ = lean_ctor_get(v_v_1727_, 1);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_v_1727_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1739_ = v_v_1727_;
v_isShared_1740_ = v_isSharedCheck_1745_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_b_1737_);
lean_inc(v_info_1736_);
lean_dec(v_v_1727_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1745_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; lean_object* v___x_1743_; 
lean_inc_ref(v_f_1722_);
v___x_1741_ = l_Lean_IR_MapVars_mapFnBody(v_f_1722_, v_b_1737_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 1, v___x_1741_);
v___x_1743_ = v___x_1739_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_info_1736_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v___x_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
v___y_1731_ = v___x_1743_;
goto v___jp_1730_;
}
}
}
else
{
lean_object* v_b_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1754_; 
v_b_1746_ = lean_ctor_get(v_v_1727_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_v_1727_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1748_ = v_v_1727_;
v_isShared_1749_ = v_isSharedCheck_1754_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_b_1746_);
lean_dec(v_v_1727_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1754_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1752_; 
lean_inc_ref(v_f_1722_);
v___x_1750_ = l_Lean_IR_MapVars_mapFnBody(v_f_1722_, v_b_1746_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1750_);
v___x_1752_ = v___x_1748_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
v___y_1731_ = v___x_1752_;
goto v___jp_1730_;
}
}
}
v___jp_1730_:
{
size_t v___x_1732_; size_t v___x_1733_; lean_object* v___x_1734_; 
v___x_1732_ = ((size_t)1ULL);
v___x_1733_ = lean_usize_add(v_i_1724_, v___x_1732_);
v___x_1734_ = lean_array_uset(v_bs_x27_1729_, v_i_1724_, v___y_1731_);
v_i_1724_ = v___x_1733_;
v_bs_1725_ = v___x_1734_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0___boxed(lean_object* v_f_1755_, lean_object* v_sz_1756_, lean_object* v_i_1757_, lean_object* v_bs_1758_){
_start:
{
size_t v_sz_boxed_1759_; size_t v_i_boxed_1760_; lean_object* v_res_1761_; 
v_sz_boxed_1759_ = lean_unbox_usize(v_sz_1756_);
lean_dec(v_sz_1756_);
v_i_boxed_1760_ = lean_unbox_usize(v_i_1757_);
lean_dec(v_i_1757_);
v_res_1761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(v_f_1755_, v_sz_boxed_1759_, v_i_boxed_1760_, v_bs_1758_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_mapVars(lean_object* v_f_1762_, lean_object* v_b_1763_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_IR_MapVars_mapFnBody(v_f_1762_, v_b_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lam__0(lean_object* v_x_1765_, lean_object* v_y_1766_, lean_object* v_z_1767_){
_start:
{
uint8_t v___x_1768_; 
v___x_1768_ = l_Lean_IR_instBEqVarId_beq(v_x_1765_, v_z_1767_);
if (v___x_1768_ == 0)
{
lean_inc(v_z_1767_);
return v_z_1767_;
}
else
{
lean_inc(v_y_1766_);
return v_y_1766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lam__0___boxed(lean_object* v_x_1769_, lean_object* v_y_1770_, lean_object* v_z_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_IR_FnBody_replaceVar___lam__0(v_x_1769_, v_y_1770_, v_z_1771_);
lean_dec(v_z_1771_);
lean_dec(v_y_1770_);
lean_dec(v_x_1769_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar(lean_object* v_x_1773_, lean_object* v_y_1774_, lean_object* v_b_1775_){
_start:
{
lean_object* v___f_1776_; lean_object* v___x_1777_; 
v___f_1776_ = lean_alloc_closure((void*)(l_Lean_IR_FnBody_replaceVar___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1776_, 0, v_x_1773_);
lean_closure_set(v___f_1776_, 1, v_y_1774_);
v___x_1777_ = l_Lean_IR_MapVars_mapFnBody(v___f_1776_, v_b_1775_);
return v___x_1777_;
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
