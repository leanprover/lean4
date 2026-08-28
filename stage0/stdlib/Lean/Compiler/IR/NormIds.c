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
lean_object* v___x_339_; lean_object* v_x_340_; lean_object* v___x_341_; lean_object* v_fst_342_; uint8_t v___x_343_; 
v___x_339_ = lean_array_uget_borrowed(v_as_334_, v_i_335_);
v_x_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_x_340_);
v___x_341_ = l_Lean_IR_UniqueIds_checkId(v_x_340_, v___y_337_);
v_fst_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_fst_342_);
v___x_343_ = lean_unbox(v_fst_342_);
lean_dec(v_fst_342_);
if (v___x_343_ == 0)
{
lean_object* v_snd_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_353_; 
v_snd_344_ = lean_ctor_get(v___x_341_, 1);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_353_ == 0)
{
lean_object* v_unused_354_; 
v_unused_354_ = lean_ctor_get(v___x_341_, 0);
lean_dec(v_unused_354_);
v___x_346_ = v___x_341_;
v_isShared_347_ = v_isSharedCheck_353_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_snd_344_);
lean_dec(v___x_341_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_353_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
uint8_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_351_; 
v___x_348_ = 1;
v___x_349_ = lean_box(v___x_348_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_349_);
v___x_351_ = v___x_346_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_snd_344_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
else
{
lean_object* v_snd_355_; size_t v___x_356_; size_t v___x_357_; 
v_snd_355_ = lean_ctor_get(v___x_341_, 1);
lean_inc(v_snd_355_);
lean_dec_ref(v___x_341_);
v___x_356_ = ((size_t)1ULL);
v___x_357_ = lean_usize_add(v_i_335_, v___x_356_);
v_i_335_ = v___x_357_;
v___y_337_ = v_snd_355_;
goto _start;
}
}
else
{
uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = 0;
v___x_360_ = lean_box(v___x_359_);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v___y_337_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0___boxed(lean_object* v_as_362_, lean_object* v_i_363_, lean_object* v_stop_364_, lean_object* v___y_365_){
_start:
{
size_t v_i_boxed_366_; size_t v_stop_boxed_367_; lean_object* v_res_368_; 
v_i_boxed_366_ = lean_unbox_usize(v_i_363_);
lean_dec(v_i_363_);
v_stop_boxed_367_ = lean_unbox_usize(v_stop_364_);
lean_dec(v_stop_364_);
v_res_368_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0(v_as_362_, v_i_boxed_366_, v_stop_boxed_367_, v___y_365_);
lean_dec_ref(v_as_362_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkParams(lean_object* v_ps_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___y_372_; lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = lean_array_get_size(v_ps_369_);
v___x_378_ = lean_nat_dec_lt(v___x_376_, v___x_377_);
if (v___x_378_ == 0)
{
v___y_372_ = v_a_370_;
goto v___jp_371_;
}
else
{
if (v___x_378_ == 0)
{
v___y_372_ = v_a_370_;
goto v___jp_371_;
}
else
{
size_t v___x_379_; size_t v___x_380_; lean_object* v___x_381_; lean_object* v_fst_382_; uint8_t v___x_383_; 
v___x_379_ = ((size_t)0ULL);
v___x_380_ = lean_usize_of_nat(v___x_377_);
v___x_381_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0(v_ps_369_, v___x_379_, v___x_380_, v_a_370_);
v_fst_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_fst_382_);
v___x_383_ = lean_unbox(v_fst_382_);
lean_dec(v_fst_382_);
if (v___x_383_ == 0)
{
lean_object* v_snd_384_; 
v_snd_384_ = lean_ctor_get(v___x_381_, 1);
lean_inc(v_snd_384_);
lean_dec_ref(v___x_381_);
v___y_372_ = v_snd_384_;
goto v___jp_371_;
}
else
{
lean_object* v_snd_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_394_; 
v_snd_385_ = lean_ctor_get(v___x_381_, 1);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_394_ == 0)
{
lean_object* v_unused_395_; 
v_unused_395_ = lean_ctor_get(v___x_381_, 0);
lean_dec(v_unused_395_);
v___x_387_ = v___x_381_;
v_isShared_388_ = v_isSharedCheck_394_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_snd_385_);
lean_dec(v___x_381_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_394_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
uint8_t v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_389_ = 0;
v___x_390_ = lean_box(v___x_389_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v___x_390_);
v___x_392_ = v___x_387_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_snd_385_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
v___jp_371_:
{
uint8_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = 1;
v___x_374_ = lean_box(v___x_373_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v___y_372_);
return v___x_375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkParams___boxed(lean_object* v_ps_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_IR_UniqueIds_checkParams(v_ps_396_, v_a_397_);
lean_dec_ref(v_ps_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkFnBody(lean_object* v_x_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___y_402_; 
switch(lean_obj_tag(v_x_399_))
{
case 0:
{
lean_object* v_x_406_; lean_object* v_b_407_; lean_object* v___x_408_; lean_object* v_fst_409_; uint8_t v___x_410_; 
v_x_406_ = lean_ctor_get(v_x_399_, 0);
lean_inc(v_x_406_);
v_b_407_ = lean_ctor_get(v_x_399_, 3);
lean_inc(v_b_407_);
lean_dec_ref_known(v_x_399_, 4);
v___x_408_ = l_Lean_IR_UniqueIds_checkId(v_x_406_, v_a_400_);
v_fst_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_fst_409_);
v___x_410_ = lean_unbox(v_fst_409_);
lean_dec(v_fst_409_);
if (v___x_410_ == 0)
{
lean_dec(v_b_407_);
return v___x_408_;
}
else
{
lean_object* v_snd_411_; 
v_snd_411_ = lean_ctor_get(v___x_408_, 1);
lean_inc(v_snd_411_);
lean_dec_ref(v___x_408_);
v_x_399_ = v_b_407_;
v_a_400_ = v_snd_411_;
goto _start;
}
}
case 1:
{
lean_object* v_j_413_; lean_object* v_xs_414_; lean_object* v_b_415_; lean_object* v___x_416_; lean_object* v_fst_417_; uint8_t v___x_418_; 
v_j_413_ = lean_ctor_get(v_x_399_, 0);
lean_inc(v_j_413_);
v_xs_414_ = lean_ctor_get(v_x_399_, 1);
lean_inc_ref(v_xs_414_);
v_b_415_ = lean_ctor_get(v_x_399_, 3);
lean_inc(v_b_415_);
lean_dec_ref_known(v_x_399_, 4);
v___x_416_ = l_Lean_IR_UniqueIds_checkId(v_j_413_, v_a_400_);
v_fst_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_fst_417_);
v___x_418_ = lean_unbox(v_fst_417_);
lean_dec(v_fst_417_);
if (v___x_418_ == 0)
{
lean_dec(v_b_415_);
lean_dec_ref(v_xs_414_);
return v___x_416_;
}
else
{
lean_object* v_snd_419_; lean_object* v___x_420_; lean_object* v_fst_421_; uint8_t v___x_422_; 
v_snd_419_ = lean_ctor_get(v___x_416_, 1);
lean_inc(v_snd_419_);
lean_dec_ref(v___x_416_);
v___x_420_ = l_Lean_IR_UniqueIds_checkParams(v_xs_414_, v_snd_419_);
lean_dec_ref(v_xs_414_);
v_fst_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_fst_421_);
v___x_422_ = lean_unbox(v_fst_421_);
lean_dec(v_fst_421_);
if (v___x_422_ == 0)
{
lean_dec(v_b_415_);
return v___x_420_;
}
else
{
lean_object* v_snd_423_; 
v_snd_423_ = lean_ctor_get(v___x_420_, 1);
lean_inc(v_snd_423_);
lean_dec_ref(v___x_420_);
v_x_399_ = v_b_415_;
v_a_400_ = v_snd_423_;
goto _start;
}
}
}
case 9:
{
lean_object* v_cs_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v_cs_425_ = lean_ctor_get(v_x_399_, 3);
lean_inc_ref(v_cs_425_);
lean_dec_ref_known(v_x_399_, 4);
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_array_get_size(v_cs_425_);
v___x_428_ = lean_nat_dec_lt(v___x_426_, v___x_427_);
if (v___x_428_ == 0)
{
lean_dec_ref(v_cs_425_);
v___y_402_ = v_a_400_;
goto v___jp_401_;
}
else
{
if (v___x_428_ == 0)
{
lean_dec_ref(v_cs_425_);
v___y_402_ = v_a_400_;
goto v___jp_401_;
}
else
{
size_t v___x_429_; size_t v___x_430_; lean_object* v___x_431_; lean_object* v_fst_432_; uint8_t v___x_433_; 
v___x_429_ = ((size_t)0ULL);
v___x_430_ = lean_usize_of_nat(v___x_427_);
v___x_431_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(v_cs_425_, v___x_429_, v___x_430_, v_a_400_);
lean_dec_ref(v_cs_425_);
v_fst_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_fst_432_);
v___x_433_ = lean_unbox(v_fst_432_);
lean_dec(v_fst_432_);
if (v___x_433_ == 0)
{
lean_object* v_snd_434_; 
v_snd_434_ = lean_ctor_get(v___x_431_, 1);
lean_inc(v_snd_434_);
lean_dec_ref(v___x_431_);
v___y_402_ = v_snd_434_;
goto v___jp_401_;
}
else
{
lean_object* v_snd_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_444_; 
v_snd_435_ = lean_ctor_get(v___x_431_, 1);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; 
v_unused_445_ = lean_ctor_get(v___x_431_, 0);
lean_dec(v_unused_445_);
v___x_437_ = v___x_431_;
v_isShared_438_ = v_isSharedCheck_444_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_snd_435_);
lean_dec(v___x_431_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_444_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
uint8_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_439_ = 0;
v___x_440_ = lean_box(v___x_439_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_440_);
v___x_442_ = v___x_437_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_snd_435_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
}
default: 
{
uint8_t v___x_446_; 
v___x_446_ = l_Lean_IR_FnBody_isTerminal(v_x_399_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_IR_FnBody_body(v_x_399_);
lean_dec(v_x_399_);
v_x_399_ = v___x_447_;
goto _start;
}
else
{
lean_object* v___x_449_; lean_object* v___x_450_; 
lean_dec(v_x_399_);
v___x_449_ = lean_box(v___x_446_);
v___x_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set(v___x_450_, 1, v_a_400_);
return v___x_450_;
}
}
}
v___jp_401_:
{
uint8_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = 1;
v___x_404_ = lean_box(v___x_403_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___y_402_);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(lean_object* v_as_451_, size_t v_i_452_, size_t v_stop_453_, lean_object* v___y_454_){
_start:
{
uint8_t v___x_455_; 
v___x_455_ = lean_usize_dec_eq(v_i_452_, v_stop_453_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v_fst_459_; uint8_t v___x_460_; 
v___x_456_ = lean_array_uget_borrowed(v_as_451_, v_i_452_);
v___x_457_ = l_Lean_IR_Alt_body(v___x_456_);
v___x_458_ = l_Lean_IR_UniqueIds_checkFnBody(v___x_457_, v___y_454_);
v_fst_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_fst_459_);
v___x_460_ = lean_unbox(v_fst_459_);
lean_dec(v_fst_459_);
if (v___x_460_ == 0)
{
lean_object* v_snd_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_470_; 
v_snd_461_ = lean_ctor_get(v___x_458_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; 
v_unused_471_ = lean_ctor_get(v___x_458_, 0);
lean_dec(v_unused_471_);
v___x_463_ = v___x_458_;
v_isShared_464_ = v_isSharedCheck_470_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_snd_461_);
lean_dec(v___x_458_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_470_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_465_ = 1;
v___x_466_ = lean_box(v___x_465_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_466_);
v___x_468_ = v___x_463_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_snd_461_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
else
{
lean_object* v_snd_472_; size_t v___x_473_; size_t v___x_474_; 
v_snd_472_ = lean_ctor_get(v___x_458_, 1);
lean_inc(v_snd_472_);
lean_dec_ref(v___x_458_);
v___x_473_ = ((size_t)1ULL);
v___x_474_ = lean_usize_add(v_i_452_, v___x_473_);
v_i_452_ = v___x_474_;
v___y_454_ = v_snd_472_;
goto _start;
}
}
else
{
uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = 0;
v___x_477_ = lean_box(v___x_476_);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v___y_454_);
return v___x_478_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0___boxed(lean_object* v_as_479_, lean_object* v_i_480_, lean_object* v_stop_481_, lean_object* v___y_482_){
_start:
{
size_t v_i_boxed_483_; size_t v_stop_boxed_484_; lean_object* v_res_485_; 
v_i_boxed_483_ = lean_unbox_usize(v_i_480_);
lean_dec(v_i_480_);
v_stop_boxed_484_ = lean_unbox_usize(v_stop_481_);
lean_dec(v_stop_481_);
v_res_485_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(v_as_479_, v_i_boxed_483_, v_stop_boxed_484_, v___y_482_);
lean_dec_ref(v_as_479_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkDecl(lean_object* v_x_486_, lean_object* v_a_487_){
_start:
{
if (lean_obj_tag(v_x_486_) == 0)
{
lean_object* v_xs_488_; lean_object* v_body_489_; lean_object* v___x_490_; lean_object* v_fst_491_; uint8_t v___x_492_; 
v_xs_488_ = lean_ctor_get(v_x_486_, 1);
lean_inc_ref(v_xs_488_);
v_body_489_ = lean_ctor_get(v_x_486_, 3);
lean_inc(v_body_489_);
lean_dec_ref_known(v_x_486_, 5);
v___x_490_ = l_Lean_IR_UniqueIds_checkParams(v_xs_488_, v_a_487_);
lean_dec_ref(v_xs_488_);
v_fst_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_fst_491_);
v___x_492_ = lean_unbox(v_fst_491_);
lean_dec(v_fst_491_);
if (v___x_492_ == 0)
{
lean_dec(v_body_489_);
return v___x_490_;
}
else
{
lean_object* v_snd_493_; lean_object* v___x_494_; 
v_snd_493_ = lean_ctor_get(v___x_490_, 1);
lean_inc(v_snd_493_);
lean_dec_ref(v___x_490_);
v___x_494_ = l_Lean_IR_UniqueIds_checkFnBody(v_body_489_, v_snd_493_);
return v___x_494_;
}
}
else
{
lean_object* v_xs_495_; lean_object* v___x_496_; 
v_xs_495_ = lean_ctor_get(v_x_486_, 1);
lean_inc_ref(v_xs_495_);
lean_dec_ref_known(v_x_486_, 4);
v___x_496_ = l_Lean_IR_UniqueIds_checkParams(v_xs_495_, v_a_487_);
lean_dec_ref(v_xs_495_);
return v___x_496_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Decl_uniqueIds(lean_object* v_d_497_){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v_fst_500_; uint8_t v___x_501_; 
v___x_498_ = lean_box(1);
v___x_499_ = l_Lean_IR_UniqueIds_checkDecl(v_d_497_, v___x_498_);
v_fst_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_fst_500_);
lean_dec_ref(v___x_499_);
v___x_501_ = lean_unbox(v_fst_500_);
lean_dec(v_fst_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_uniqueIds___boxed(lean_object* v_d_502_){
_start:
{
uint8_t v_res_503_; lean_object* v_r_504_; 
v_res_503_ = l_Lean_IR_Decl_uniqueIds(v_d_502_);
v_r_504_ = lean_box(v_res_503_);
return v_r_504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(lean_object* v_t_505_, lean_object* v_k_506_){
_start:
{
if (lean_obj_tag(v_t_505_) == 0)
{
lean_object* v_k_507_; lean_object* v_v_508_; lean_object* v_l_509_; lean_object* v_r_510_; uint8_t v___x_511_; 
v_k_507_ = lean_ctor_get(v_t_505_, 1);
v_v_508_ = lean_ctor_get(v_t_505_, 2);
v_l_509_ = lean_ctor_get(v_t_505_, 3);
v_r_510_ = lean_ctor_get(v_t_505_, 4);
v___x_511_ = lean_nat_dec_lt(v_k_506_, v_k_507_);
if (v___x_511_ == 0)
{
uint8_t v___x_512_; 
v___x_512_ = lean_nat_dec_eq(v_k_506_, v_k_507_);
if (v___x_512_ == 0)
{
v_t_505_ = v_r_510_;
goto _start;
}
else
{
lean_object* v___x_514_; 
lean_inc(v_v_508_);
v___x_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_514_, 0, v_v_508_);
return v___x_514_;
}
}
else
{
v_t_505_ = v_l_509_;
goto _start;
}
}
else
{
lean_object* v___x_516_; 
v___x_516_ = lean_box(0);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg___boxed(lean_object* v_t_517_, lean_object* v_k_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_t_517_, v_k_518_);
lean_dec(v_k_518_);
lean_dec(v_t_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normIndex(lean_object* v_x_520_, lean_object* v_m_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_m_521_, v_x_520_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_inc(v_x_520_);
return v_x_520_;
}
else
{
lean_object* v_val_523_; 
v_val_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_val_523_);
lean_dec_ref_known(v___x_522_, 1);
return v_val_523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normIndex___boxed(lean_object* v_x_524_, lean_object* v_m_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_IR_NormalizeIds_normIndex(v_x_524_, v_m_525_);
lean_dec(v_m_525_);
lean_dec(v_x_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0(lean_object* v_00_u03b4_527_, lean_object* v_t_528_, lean_object* v_k_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_t_528_, v_k_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___boxed(lean_object* v_00_u03b4_531_, lean_object* v_t_532_, lean_object* v_k_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0(v_00_u03b4_531_, v_t_532_, v_k_533_);
lean_dec(v_k_533_);
lean_dec(v_t_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normVar(lean_object* v_x_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_IR_NormalizeIds_normIndex(v_x_535_, v_a_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normVar___boxed(lean_object* v_x_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_IR_NormalizeIds_normVar(v_x_538_, v_a_539_);
lean_dec(v_a_539_);
lean_dec(v_x_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normJP(lean_object* v_x_541_, lean_object* v_a_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_IR_NormalizeIds_normIndex(v_x_541_, v_a_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normJP___boxed(lean_object* v_x_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_IR_NormalizeIds_normJP(v_x_544_, v_a_545_);
lean_dec(v_a_545_);
lean_dec(v_x_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArg(lean_object* v_x_547_, lean_object* v_a_548_){
_start:
{
if (lean_obj_tag(v_x_547_) == 0)
{
lean_object* v_id_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_557_; 
v_id_549_ = lean_ctor_get(v_x_547_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v_x_547_);
if (v_isSharedCheck_557_ == 0)
{
v___x_551_ = v_x_547_;
v_isShared_552_ = v_isSharedCheck_557_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_id_549_);
lean_dec(v_x_547_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_557_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = l_Lean_IR_NormalizeIds_normIndex(v_id_549_, v_a_548_);
lean_dec(v_id_549_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_553_);
v___x_555_ = v___x_551_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
else
{
return v_x_547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArg___boxed(lean_object* v_x_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_IR_NormalizeIds_normArg(v_x_558_, v_a_559_);
lean_dec(v_a_559_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(lean_object* v_m_561_, size_t v_sz_562_, size_t v_i_563_, lean_object* v_bs_564_){
_start:
{
uint8_t v___x_565_; 
v___x_565_ = lean_usize_dec_lt(v_i_563_, v_sz_562_);
if (v___x_565_ == 0)
{
return v_bs_564_;
}
else
{
lean_object* v_v_566_; lean_object* v___x_567_; lean_object* v_bs_x27_568_; lean_object* v___x_569_; size_t v___x_570_; size_t v___x_571_; lean_object* v___x_572_; 
v_v_566_ = lean_array_uget(v_bs_564_, v_i_563_);
v___x_567_ = lean_unsigned_to_nat(0u);
v_bs_x27_568_ = lean_array_uset(v_bs_564_, v_i_563_, v___x_567_);
v___x_569_ = l_Lean_IR_NormalizeIds_normArg(v_v_566_, v_m_561_);
v___x_570_ = ((size_t)1ULL);
v___x_571_ = lean_usize_add(v_i_563_, v___x_570_);
v___x_572_ = lean_array_uset(v_bs_x27_568_, v_i_563_, v___x_569_);
v_i_563_ = v___x_571_;
v_bs_564_ = v___x_572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0___boxed(lean_object* v_m_574_, lean_object* v_sz_575_, lean_object* v_i_576_, lean_object* v_bs_577_){
_start:
{
size_t v_sz_boxed_578_; size_t v_i_boxed_579_; lean_object* v_res_580_; 
v_sz_boxed_578_ = lean_unbox_usize(v_sz_575_);
lean_dec(v_sz_575_);
v_i_boxed_579_ = lean_unbox_usize(v_i_576_);
lean_dec(v_i_576_);
v_res_580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(v_m_574_, v_sz_boxed_578_, v_i_boxed_579_, v_bs_577_);
lean_dec(v_m_574_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArgs(lean_object* v_as_581_, lean_object* v_m_582_){
_start:
{
size_t v_sz_583_; size_t v___x_584_; lean_object* v___x_585_; 
v_sz_583_ = lean_array_size(v_as_581_);
v___x_584_ = ((size_t)0ULL);
v___x_585_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(v_m_582_, v_sz_583_, v___x_584_, v_as_581_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArgs___boxed(lean_object* v_as_586_, lean_object* v_m_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_IR_NormalizeIds_normArgs(v_as_586_, v_m_587_);
lean_dec(v_m_587_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normExpr(lean_object* v_x_589_, lean_object* v_x_590_){
_start:
{
switch(lean_obj_tag(v_x_589_))
{
case 0:
{
lean_object* v_i_591_; lean_object* v_ys_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_600_; 
v_i_591_ = lean_ctor_get(v_x_589_, 0);
v_ys_592_ = lean_ctor_get(v_x_589_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_600_ == 0)
{
v___x_594_ = v_x_589_;
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_ys_592_);
lean_inc(v_i_591_);
lean_dec(v_x_589_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_592_, v_x_590_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 1, v___x_596_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_i_591_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
case 1:
{
lean_object* v_n_601_; lean_object* v_x_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_610_; 
v_n_601_ = lean_ctor_get(v_x_589_, 0);
v_x_602_ = lean_ctor_get(v_x_589_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_610_ == 0)
{
v___x_604_ = v_x_589_;
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_x_602_);
lean_inc(v_n_601_);
lean_dec(v_x_589_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_606_ = l_Lean_IR_NormalizeIds_normIndex(v_x_602_, v_x_590_);
lean_dec(v_x_602_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 1, v___x_606_);
v___x_608_ = v___x_604_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_n_601_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
case 2:
{
lean_object* v_x_611_; lean_object* v_i_612_; uint8_t v_updtHeader_613_; lean_object* v_ys_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_623_; 
v_x_611_ = lean_ctor_get(v_x_589_, 0);
v_i_612_ = lean_ctor_get(v_x_589_, 1);
v_updtHeader_613_ = lean_ctor_get_uint8(v_x_589_, sizeof(void*)*3);
v_ys_614_ = lean_ctor_get(v_x_589_, 2);
v_isSharedCheck_623_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_623_ == 0)
{
v___x_616_ = v_x_589_;
v_isShared_617_ = v_isSharedCheck_623_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_ys_614_);
lean_inc(v_i_612_);
lean_inc(v_x_611_);
lean_dec(v_x_589_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_623_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_618_ = l_Lean_IR_NormalizeIds_normIndex(v_x_611_, v_x_590_);
lean_dec(v_x_611_);
v___x_619_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_614_, v_x_590_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 2, v___x_619_);
lean_ctor_set(v___x_616_, 0, v___x_618_);
v___x_621_ = v___x_616_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_618_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_i_612_);
lean_ctor_set(v_reuseFailAlloc_622_, 2, v___x_619_);
lean_ctor_set_uint8(v_reuseFailAlloc_622_, sizeof(void*)*3, v_updtHeader_613_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
case 3:
{
lean_object* v_i_624_; lean_object* v_x_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_633_; 
v_i_624_ = lean_ctor_get(v_x_589_, 0);
v_x_625_ = lean_ctor_get(v_x_589_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_633_ == 0)
{
v___x_627_ = v_x_589_;
v_isShared_628_ = v_isSharedCheck_633_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_x_625_);
lean_inc(v_i_624_);
lean_dec(v_x_589_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_633_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_629_ = l_Lean_IR_NormalizeIds_normIndex(v_x_625_, v_x_590_);
lean_dec(v_x_625_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v___x_629_);
v___x_631_ = v___x_627_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_i_624_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
case 4:
{
lean_object* v_i_634_; lean_object* v_x_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_643_; 
v_i_634_ = lean_ctor_get(v_x_589_, 0);
v_x_635_ = lean_ctor_get(v_x_589_, 1);
v_isSharedCheck_643_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_643_ == 0)
{
v___x_637_ = v_x_589_;
v_isShared_638_ = v_isSharedCheck_643_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_x_635_);
lean_inc(v_i_634_);
lean_dec(v_x_589_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_643_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_639_ = l_Lean_IR_NormalizeIds_normIndex(v_x_635_, v_x_590_);
lean_dec(v_x_635_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v___x_639_);
v___x_641_ = v___x_637_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_i_634_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
case 5:
{
lean_object* v_n_644_; lean_object* v_offset_645_; lean_object* v_x_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_654_; 
v_n_644_ = lean_ctor_get(v_x_589_, 0);
v_offset_645_ = lean_ctor_get(v_x_589_, 1);
v_x_646_ = lean_ctor_get(v_x_589_, 2);
v_isSharedCheck_654_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_654_ == 0)
{
v___x_648_ = v_x_589_;
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_x_646_);
lean_inc(v_offset_645_);
lean_inc(v_n_644_);
lean_dec(v_x_589_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = l_Lean_IR_NormalizeIds_normIndex(v_x_646_, v_x_590_);
lean_dec(v_x_646_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 2, v___x_650_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_n_644_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_offset_645_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
case 6:
{
lean_object* v_c_655_; lean_object* v_ys_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_664_; 
v_c_655_ = lean_ctor_get(v_x_589_, 0);
v_ys_656_ = lean_ctor_get(v_x_589_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_664_ == 0)
{
v___x_658_ = v_x_589_;
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_ys_656_);
lean_inc(v_c_655_);
lean_dec(v_x_589_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_656_, v_x_590_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___x_660_);
v___x_662_ = v___x_658_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_c_655_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
case 7:
{
lean_object* v_c_665_; lean_object* v_ys_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_674_; 
v_c_665_ = lean_ctor_get(v_x_589_, 0);
v_ys_666_ = lean_ctor_get(v_x_589_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_674_ == 0)
{
v___x_668_ = v_x_589_;
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_ys_666_);
lean_inc(v_c_665_);
lean_dec(v_x_589_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_670_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_666_, v_x_590_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 1, v___x_670_);
v___x_672_ = v___x_668_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_c_665_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
case 8:
{
lean_object* v_x_675_; lean_object* v_ys_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_685_; 
v_x_675_ = lean_ctor_get(v_x_589_, 0);
v_ys_676_ = lean_ctor_get(v_x_589_, 1);
v_isSharedCheck_685_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_685_ == 0)
{
v___x_678_ = v_x_589_;
v_isShared_679_ = v_isSharedCheck_685_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_ys_676_);
lean_inc(v_x_675_);
lean_dec(v_x_589_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_685_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_683_; 
v___x_680_ = l_Lean_IR_NormalizeIds_normIndex(v_x_675_, v_x_590_);
lean_dec(v_x_675_);
v___x_681_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_676_, v_x_590_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 1, v___x_681_);
lean_ctor_set(v___x_678_, 0, v___x_680_);
v___x_683_ = v___x_678_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v___x_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
case 9:
{
lean_object* v_ty_686_; lean_object* v_x_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_695_; 
v_ty_686_ = lean_ctor_get(v_x_589_, 0);
v_x_687_ = lean_ctor_get(v_x_589_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_695_ == 0)
{
v___x_689_ = v_x_589_;
v_isShared_690_ = v_isSharedCheck_695_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_x_687_);
lean_inc(v_ty_686_);
lean_dec(v_x_589_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_695_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = l_Lean_IR_NormalizeIds_normIndex(v_x_687_, v_x_590_);
lean_dec(v_x_687_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v___x_691_);
v___x_693_ = v___x_689_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_ty_686_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
case 10:
{
lean_object* v_x_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_704_; 
v_x_696_ = lean_ctor_get(v_x_589_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_704_ == 0)
{
v___x_698_ = v_x_589_;
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_x_696_);
lean_dec(v_x_589_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_700_ = l_Lean_IR_NormalizeIds_normIndex(v_x_696_, v_x_590_);
lean_dec(v_x_696_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
case 11:
{
return v_x_589_;
}
default: 
{
lean_object* v_x_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_713_; 
v_x_705_ = lean_ctor_get(v_x_589_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_713_ == 0)
{
v___x_707_ = v_x_589_;
v_isShared_708_ = v_isSharedCheck_713_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_x_705_);
lean_dec(v_x_589_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_713_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_709_ = l_Lean_IR_NormalizeIds_normIndex(v_x_705_, v_x_590_);
lean_dec(v_x_705_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_709_);
v___x_711_ = v___x_707_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normExpr___boxed(lean_object* v_x_714_, lean_object* v_x_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_IR_NormalizeIds_normExpr(v_x_714_, v_x_715_);
lean_dec(v_x_715_);
return v_res_716_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_NormalizeIds_withVar___redArg___lam__0(lean_object* v_x_717_, lean_object* v_y_718_){
_start:
{
uint8_t v___x_719_; 
v___x_719_ = lean_nat_dec_lt(v_x_717_, v_y_718_);
if (v___x_719_ == 0)
{
uint8_t v___x_720_; 
v___x_720_ = lean_nat_dec_eq(v_x_717_, v_y_718_);
if (v___x_720_ == 0)
{
uint8_t v___x_721_; 
v___x_721_ = 2;
return v___x_721_;
}
else
{
uint8_t v___x_722_; 
v___x_722_ = 1;
return v___x_722_;
}
}
else
{
uint8_t v___x_723_; 
v___x_723_ = 0;
return v___x_723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg___lam__0___boxed(lean_object* v_x_724_, lean_object* v_y_725_){
_start:
{
uint8_t v_res_726_; lean_object* v_r_727_; 
v_res_726_ = l_Lean_IR_NormalizeIds_withVar___redArg___lam__0(v_x_724_, v_y_725_);
lean_dec(v_y_725_);
lean_dec(v_x_724_);
v_r_727_ = lean_box(v_res_726_);
return v_r_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg(lean_object* v_x_729_, lean_object* v_k_730_, lean_object* v_m_731_, lean_object* v_a_732_){
_start:
{
lean_object* v___f_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___f_733_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_734_ = lean_unsigned_to_nat(1u);
v___x_735_ = lean_nat_add(v_a_732_, v___x_734_);
lean_inc(v_m_731_);
lean_inc(v_a_732_);
v___x_736_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_733_, v_x_729_, v_a_732_, v_m_731_);
v___x_737_ = lean_apply_3(v_k_730_, v_a_732_, v___x_736_, v___x_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg___boxed(lean_object* v_x_738_, lean_object* v_k_739_, lean_object* v_m_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_IR_NormalizeIds_withVar___redArg(v_x_738_, v_k_739_, v_m_740_, v_a_741_);
lean_dec(v_m_740_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar(lean_object* v_00_u03b1_743_, lean_object* v_x_744_, lean_object* v_k_745_, lean_object* v_m_746_, lean_object* v_a_747_){
_start:
{
lean_object* v___f_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___f_748_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_749_ = lean_unsigned_to_nat(1u);
v___x_750_ = lean_nat_add(v_a_747_, v___x_749_);
lean_inc(v_m_746_);
lean_inc(v_a_747_);
v___x_751_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_748_, v_x_744_, v_a_747_, v_m_746_);
v___x_752_ = lean_apply_3(v_k_745_, v_a_747_, v___x_751_, v___x_750_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___boxed(lean_object* v_00_u03b1_753_, lean_object* v_x_754_, lean_object* v_k_755_, lean_object* v_m_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_IR_NormalizeIds_withVar(v_00_u03b1_753_, v_x_754_, v_k_755_, v_m_756_, v_a_757_);
lean_dec(v_m_756_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___redArg(lean_object* v_x_759_, lean_object* v_k_760_, lean_object* v_m_761_, lean_object* v_a_762_){
_start:
{
lean_object* v___f_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___f_763_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_764_ = lean_unsigned_to_nat(1u);
v___x_765_ = lean_nat_add(v_a_762_, v___x_764_);
lean_inc(v_m_761_);
lean_inc(v_a_762_);
v___x_766_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_763_, v_x_759_, v_a_762_, v_m_761_);
v___x_767_ = lean_apply_3(v_k_760_, v_a_762_, v___x_766_, v___x_765_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___redArg___boxed(lean_object* v_x_768_, lean_object* v_k_769_, lean_object* v_m_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_IR_NormalizeIds_withJP___redArg(v_x_768_, v_k_769_, v_m_770_, v_a_771_);
lean_dec(v_m_770_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP(lean_object* v_00_u03b1_773_, lean_object* v_x_774_, lean_object* v_k_775_, lean_object* v_m_776_, lean_object* v_a_777_){
_start:
{
lean_object* v___f_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___f_778_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_779_ = lean_unsigned_to_nat(1u);
v___x_780_ = lean_nat_add(v_a_777_, v___x_779_);
lean_inc(v_m_776_);
lean_inc(v_a_777_);
v___x_781_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_778_, v_x_774_, v_a_777_, v_m_776_);
v___x_782_ = lean_apply_3(v_k_775_, v_a_777_, v___x_781_, v___x_780_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___boxed(lean_object* v_00_u03b1_783_, lean_object* v_x_784_, lean_object* v_k_785_, lean_object* v_m_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_IR_NormalizeIds_withJP(v_00_u03b1_783_, v_x_784_, v_k_785_, v_m_786_, v_a_787_);
lean_dec(v_m_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__0(lean_object* v_fst_789_, lean_object* v_x_790_){
_start:
{
lean_object* v_x_791_; uint8_t v_borrow_792_; lean_object* v_ty_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_801_; 
v_x_791_ = lean_ctor_get(v_x_790_, 0);
v_borrow_792_ = lean_ctor_get_uint8(v_x_790_, sizeof(void*)*2);
v_ty_793_ = lean_ctor_get(v_x_790_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_x_790_);
if (v_isSharedCheck_801_ == 0)
{
v___x_795_ = v_x_790_;
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_ty_793_);
lean_inc(v_x_791_);
lean_dec(v_x_790_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = l_Lean_IR_NormalizeIds_normIndex(v_x_791_, v_fst_789_);
lean_dec(v_x_791_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_ty_793_);
lean_ctor_set_uint8(v_reuseFailAlloc_800_, sizeof(void*)*2, v_borrow_792_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed(lean_object* v_fst_802_, lean_object* v_x_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_IR_NormalizeIds_withParams___redArg___lam__0(v_fst_802_, v_x_803_);
lean_dec(v_fst_802_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__2(lean_object* v___f_805_, lean_object* v_m_806_, lean_object* v_p_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v_x_809_ = lean_ctor_get(v_p_807_, 0);
lean_inc(v_x_809_);
lean_dec_ref(v_p_807_);
v___x_810_ = lean_unsigned_to_nat(1u);
v___x_811_ = lean_nat_add(v___y_808_, v___x_810_);
v___x_812_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_805_, v_x_809_, v___y_808_, v_m_806_);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v___x_811_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg(lean_object* v_ps_861_, lean_object* v_k_862_, lean_object* v_m_863_, lean_object* v_a_864_){
_start:
{
lean_object* v___x_865_; lean_object* v_fst_867_; lean_object* v_snd_868_; lean_object* v___y_875_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_865_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__9));
v___x_878_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__19));
v___x_879_ = lean_unsigned_to_nat(0u);
v___x_880_ = lean_array_get_size(v_ps_861_);
v___x_881_ = lean_nat_dec_lt(v___x_879_, v___x_880_);
if (v___x_881_ == 0)
{
lean_inc(v_m_863_);
v_fst_867_ = v_m_863_;
v_snd_868_ = v_a_864_;
goto v___jp_866_;
}
else
{
lean_object* v___f_882_; uint8_t v___x_883_; 
v___f_882_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__20));
v___x_883_ = lean_nat_dec_le(v___x_880_, v___x_880_);
if (v___x_883_ == 0)
{
if (v___x_881_ == 0)
{
lean_inc(v_m_863_);
v_fst_867_ = v_m_863_;
v_snd_868_ = v_a_864_;
goto v___jp_866_;
}
else
{
size_t v___x_884_; size_t v___x_885_; lean_object* v___x_787__overap_886_; lean_object* v___x_887_; 
v___x_884_ = ((size_t)0ULL);
v___x_885_ = lean_usize_of_nat(v___x_880_);
lean_inc(v_m_863_);
lean_inc_ref(v_ps_861_);
v___x_787__overap_886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_878_, v___f_882_, v_ps_861_, v___x_884_, v___x_885_, v_m_863_);
v___x_887_ = lean_apply_1(v___x_787__overap_886_, v_a_864_);
v___y_875_ = v___x_887_;
goto v___jp_874_;
}
}
else
{
size_t v___x_888_; size_t v___x_889_; lean_object* v___x_791__overap_890_; lean_object* v___x_891_; 
v___x_888_ = ((size_t)0ULL);
v___x_889_ = lean_usize_of_nat(v___x_880_);
lean_inc(v_m_863_);
lean_inc_ref(v_ps_861_);
v___x_791__overap_890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_878_, v___f_882_, v_ps_861_, v___x_888_, v___x_889_, v_m_863_);
v___x_891_ = lean_apply_1(v___x_791__overap_890_, v_a_864_);
v___y_875_ = v___x_891_;
goto v___jp_874_;
}
}
v___jp_866_:
{
lean_object* v___f_869_; size_t v_sz_870_; size_t v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
lean_inc(v_fst_867_);
v___f_869_ = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_869_, 0, v_fst_867_);
v_sz_870_ = lean_array_size(v_ps_861_);
v___x_871_ = ((size_t)0ULL);
v___x_872_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_865_, v___f_869_, v_sz_870_, v___x_871_, v_ps_861_);
v___x_873_ = lean_apply_3(v_k_862_, v___x_872_, v_fst_867_, v_snd_868_);
return v___x_873_;
}
v___jp_874_:
{
lean_object* v_fst_876_; lean_object* v_snd_877_; 
v_fst_876_ = lean_ctor_get(v___y_875_, 0);
lean_inc(v_fst_876_);
v_snd_877_ = lean_ctor_get(v___y_875_, 1);
lean_inc(v_snd_877_);
lean_dec_ref(v___y_875_);
v_fst_867_ = v_fst_876_;
v_snd_868_ = v_snd_877_;
goto v___jp_866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___boxed(lean_object* v_ps_892_, lean_object* v_k_893_, lean_object* v_m_894_, lean_object* v_a_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_IR_NormalizeIds_withParams___redArg(v_ps_892_, v_k_893_, v_m_894_, v_a_895_);
lean_dec(v_m_894_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams(lean_object* v_00_u03b1_897_, lean_object* v_ps_898_, lean_object* v_k_899_, lean_object* v_m_900_, lean_object* v_a_901_){
_start:
{
lean_object* v___x_902_; lean_object* v_fst_904_; lean_object* v_snd_905_; lean_object* v___y_912_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_902_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__9));
v___x_915_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__19));
v___x_916_ = lean_unsigned_to_nat(0u);
v___x_917_ = lean_array_get_size(v_ps_898_);
v___x_918_ = lean_nat_dec_lt(v___x_916_, v___x_917_);
if (v___x_918_ == 0)
{
lean_inc(v_m_900_);
v_fst_904_ = v_m_900_;
v_snd_905_ = v_a_901_;
goto v___jp_903_;
}
else
{
lean_object* v___f_919_; uint8_t v___x_920_; 
v___f_919_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__20));
v___x_920_ = lean_nat_dec_le(v___x_917_, v___x_917_);
if (v___x_920_ == 0)
{
if (v___x_918_ == 0)
{
lean_inc(v_m_900_);
v_fst_904_ = v_m_900_;
v_snd_905_ = v_a_901_;
goto v___jp_903_;
}
else
{
size_t v___x_921_; size_t v___x_922_; lean_object* v___x_971__overap_923_; lean_object* v___x_924_; 
v___x_921_ = ((size_t)0ULL);
v___x_922_ = lean_usize_of_nat(v___x_917_);
lean_inc(v_m_900_);
lean_inc_ref(v_ps_898_);
v___x_971__overap_923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_915_, v___f_919_, v_ps_898_, v___x_921_, v___x_922_, v_m_900_);
v___x_924_ = lean_apply_1(v___x_971__overap_923_, v_a_901_);
v___y_912_ = v___x_924_;
goto v___jp_911_;
}
}
else
{
size_t v___x_925_; size_t v___x_926_; lean_object* v___x_974__overap_927_; lean_object* v___x_928_; 
v___x_925_ = ((size_t)0ULL);
v___x_926_ = lean_usize_of_nat(v___x_917_);
lean_inc(v_m_900_);
lean_inc_ref(v_ps_898_);
v___x_974__overap_927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_915_, v___f_919_, v_ps_898_, v___x_925_, v___x_926_, v_m_900_);
v___x_928_ = lean_apply_1(v___x_974__overap_927_, v_a_901_);
v___y_912_ = v___x_928_;
goto v___jp_911_;
}
}
v___jp_903_:
{
lean_object* v___f_906_; size_t v_sz_907_; size_t v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
lean_inc(v_fst_904_);
v___f_906_ = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_906_, 0, v_fst_904_);
v_sz_907_ = lean_array_size(v_ps_898_);
v___x_908_ = ((size_t)0ULL);
v___x_909_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_902_, v___f_906_, v_sz_907_, v___x_908_, v_ps_898_);
v___x_910_ = lean_apply_3(v_k_899_, v___x_909_, v_fst_904_, v_snd_905_);
return v___x_910_;
}
v___jp_911_:
{
lean_object* v_fst_913_; lean_object* v_snd_914_; 
v_fst_913_ = lean_ctor_get(v___y_912_, 0);
lean_inc(v_fst_913_);
v_snd_914_ = lean_ctor_get(v___y_912_, 1);
lean_inc(v_snd_914_);
lean_dec_ref(v___y_912_);
v_fst_904_ = v_fst_913_;
v_snd_905_ = v_snd_914_;
goto v___jp_903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___boxed(lean_object* v_00_u03b1_929_, lean_object* v_ps_930_, lean_object* v_k_931_, lean_object* v_m_932_, lean_object* v_a_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_IR_NormalizeIds_withParams(v_00_u03b1_929_, v_ps_930_, v_k_931_, v_m_932_, v_a_933_);
lean_dec(v_m_932_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_instMonadLiftMN___lam__0(lean_object* v_00_u03b1_935_, lean_object* v_x_936_, lean_object* v_m_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_apply_1(v_x_936_, v_m_937_);
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v___y_938_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(lean_object* v_fst_943_, size_t v_sz_944_, size_t v_i_945_, lean_object* v_bs_946_){
_start:
{
uint8_t v___x_947_; 
v___x_947_ = lean_usize_dec_lt(v_i_945_, v_sz_944_);
if (v___x_947_ == 0)
{
return v_bs_946_;
}
else
{
lean_object* v_v_948_; lean_object* v_x_949_; uint8_t v_borrow_950_; lean_object* v_ty_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_965_; 
v_v_948_ = lean_array_uget(v_bs_946_, v_i_945_);
v_x_949_ = lean_ctor_get(v_v_948_, 0);
v_borrow_950_ = lean_ctor_get_uint8(v_v_948_, sizeof(void*)*2);
v_ty_951_ = lean_ctor_get(v_v_948_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v_v_948_);
if (v_isSharedCheck_965_ == 0)
{
v___x_953_ = v_v_948_;
v_isShared_954_ = v_isSharedCheck_965_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_ty_951_);
lean_inc(v_x_949_);
lean_dec(v_v_948_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_965_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v_bs_x27_956_; lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_955_ = lean_unsigned_to_nat(0u);
v_bs_x27_956_ = lean_array_uset(v_bs_946_, v_i_945_, v___x_955_);
v___x_957_ = l_Lean_IR_NormalizeIds_normIndex(v_x_949_, v_fst_943_);
lean_dec(v_x_949_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v___x_957_);
v___x_959_ = v___x_953_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_ty_951_);
lean_ctor_set_uint8(v_reuseFailAlloc_964_, sizeof(void*)*2, v_borrow_950_);
v___x_959_ = v_reuseFailAlloc_964_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
size_t v___x_960_; size_t v___x_961_; lean_object* v___x_962_; 
v___x_960_ = ((size_t)1ULL);
v___x_961_ = lean_usize_add(v_i_945_, v___x_960_);
v___x_962_ = lean_array_uset(v_bs_x27_956_, v_i_945_, v___x_959_);
v_i_945_ = v___x_961_;
v_bs_946_ = v___x_962_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0___boxed(lean_object* v_fst_966_, lean_object* v_sz_967_, lean_object* v_i_968_, lean_object* v_bs_969_){
_start:
{
size_t v_sz_boxed_970_; size_t v_i_boxed_971_; lean_object* v_res_972_; 
v_sz_boxed_970_ = lean_unbox_usize(v_sz_967_);
lean_dec(v_sz_967_);
v_i_boxed_971_ = lean_unbox_usize(v_i_968_);
lean_dec(v_i_968_);
v_res_972_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(v_fst_966_, v_sz_boxed_970_, v_i_boxed_971_, v_bs_969_);
lean_dec(v_fst_966_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(lean_object* v_as_973_, size_t v_i_974_, size_t v_stop_975_, lean_object* v_b_976_, lean_object* v___y_977_){
_start:
{
uint8_t v___x_978_; 
v___x_978_ = lean_usize_dec_eq(v_i_974_, v_stop_975_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; lean_object* v_x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; size_t v___x_984_; size_t v___x_985_; 
v___x_979_ = lean_array_uget_borrowed(v_as_973_, v_i_974_);
v_x_980_ = lean_ctor_get(v___x_979_, 0);
v___x_981_ = lean_unsigned_to_nat(1u);
v___x_982_ = lean_nat_add(v___y_977_, v___x_981_);
lean_inc(v_x_980_);
v___x_983_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_x_980_, v___y_977_, v_b_976_);
v___x_984_ = ((size_t)1ULL);
v___x_985_ = lean_usize_add(v_i_974_, v___x_984_);
v_i_974_ = v___x_985_;
v_b_976_ = v___x_983_;
v___y_977_ = v___x_982_;
goto _start;
}
else
{
lean_object* v___x_987_; 
v___x_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_987_, 0, v_b_976_);
lean_ctor_set(v___x_987_, 1, v___y_977_);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1___boxed(lean_object* v_as_988_, lean_object* v_i_989_, lean_object* v_stop_990_, lean_object* v_b_991_, lean_object* v___y_992_){
_start:
{
size_t v_i_boxed_993_; size_t v_stop_boxed_994_; lean_object* v_res_995_; 
v_i_boxed_993_ = lean_unbox_usize(v_i_989_);
lean_dec(v_i_989_);
v_stop_boxed_994_ = lean_unbox_usize(v_stop_990_);
lean_dec(v_stop_990_);
v_res_995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_as_988_, v_i_boxed_993_, v_stop_boxed_994_, v_b_991_, v___y_992_);
lean_dec_ref(v_as_988_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normFnBody(lean_object* v_x_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
switch(lean_obj_tag(v_x_996_))
{
case 0:
{
lean_object* v_x_999_; lean_object* v_ty_1000_; lean_object* v_e_1001_; lean_object* v_b_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1023_; 
v_x_999_ = lean_ctor_get(v_x_996_, 0);
v_ty_1000_ = lean_ctor_get(v_x_996_, 1);
v_e_1001_ = lean_ctor_get(v_x_996_, 2);
v_b_1002_ = lean_ctor_get(v_x_996_, 3);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1004_ = v_x_996_;
v_isShared_1005_ = v_isSharedCheck_1023_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_b_1002_);
lean_inc(v_e_1001_);
lean_inc(v_ty_1000_);
lean_inc(v_x_999_);
lean_dec(v_x_996_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1023_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v_fst_1010_; lean_object* v_snd_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1022_; 
v___x_1006_ = lean_unsigned_to_nat(1u);
v___x_1007_ = lean_nat_add(v_a_998_, v___x_1006_);
lean_inc(v_a_997_);
lean_inc(v_a_998_);
v___x_1008_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_x_999_, v_a_998_, v_a_997_);
v___x_1009_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1002_, v___x_1008_, v___x_1007_);
lean_dec(v___x_1008_);
v_fst_1010_ = lean_ctor_get(v___x_1009_, 0);
v_snd_1011_ = lean_ctor_get(v___x_1009_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1013_ = v___x_1009_;
v_isShared_1014_ = v_isSharedCheck_1022_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_snd_1011_);
lean_inc(v_fst_1010_);
lean_dec(v___x_1009_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1022_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1015_ = l_Lean_IR_NormalizeIds_normExpr(v_e_1001_, v_a_997_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 3, v_fst_1010_);
lean_ctor_set(v___x_1004_, 2, v___x_1015_);
lean_ctor_set(v___x_1004_, 0, v_a_998_);
v___x_1017_ = v___x_1004_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_998_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_ty_1000_);
lean_ctor_set(v_reuseFailAlloc_1021_, 2, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1021_, 3, v_fst_1010_);
v___x_1017_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1019_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1017_);
v___x_1019_ = v___x_1013_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_snd_1011_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
case 1:
{
lean_object* v_j_1024_; lean_object* v_xs_1025_; lean_object* v_v_1026_; lean_object* v_b_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1064_; 
v_j_1024_ = lean_ctor_get(v_x_996_, 0);
v_xs_1025_ = lean_ctor_get(v_x_996_, 1);
v_v_1026_ = lean_ctor_get(v_x_996_, 2);
v_b_1027_ = lean_ctor_get(v_x_996_, 3);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1029_ = v_x_996_;
v_isShared_1030_ = v_isSharedCheck_1064_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_b_1027_);
lean_inc(v_v_1026_);
lean_inc(v_xs_1025_);
lean_inc(v_j_1024_);
lean_dec(v_x_996_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1064_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v_fst_1032_; lean_object* v_snd_1033_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1056_ = lean_unsigned_to_nat(0u);
v___x_1057_ = lean_array_get_size(v_xs_1025_);
v___x_1058_ = lean_nat_dec_lt(v___x_1056_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_inc(v_a_997_);
v_fst_1032_ = v_a_997_;
v_snd_1033_ = v_a_998_;
goto v___jp_1031_;
}
else
{
size_t v___x_1059_; size_t v___x_1060_; lean_object* v___x_1061_; lean_object* v_fst_1062_; lean_object* v_snd_1063_; 
v___x_1059_ = ((size_t)0ULL);
v___x_1060_ = lean_usize_of_nat(v___x_1057_);
lean_inc(v_a_997_);
v___x_1061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_1025_, v___x_1059_, v___x_1060_, v_a_997_, v_a_998_);
v_fst_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_fst_1062_);
v_snd_1063_ = lean_ctor_get(v___x_1061_, 1);
lean_inc(v_snd_1063_);
lean_dec_ref(v___x_1061_);
v_fst_1032_ = v_fst_1062_;
v_snd_1033_ = v_snd_1063_;
goto v___jp_1031_;
}
v___jp_1031_:
{
lean_object* v___x_1034_; lean_object* v_fst_1035_; lean_object* v_snd_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v_fst_1041_; lean_object* v_snd_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1055_; 
v___x_1034_ = l_Lean_IR_NormalizeIds_normFnBody(v_v_1026_, v_fst_1032_, v_snd_1033_);
v_fst_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_fst_1035_);
v_snd_1036_ = lean_ctor_get(v___x_1034_, 1);
lean_inc_n(v_snd_1036_, 2);
lean_dec_ref(v___x_1034_);
v___x_1037_ = lean_unsigned_to_nat(1u);
v___x_1038_ = lean_nat_add(v_snd_1036_, v___x_1037_);
lean_inc(v_a_997_);
v___x_1039_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_j_1024_, v_snd_1036_, v_a_997_);
v___x_1040_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1027_, v___x_1039_, v___x_1038_);
lean_dec(v___x_1039_);
v_fst_1041_ = lean_ctor_get(v___x_1040_, 0);
v_snd_1042_ = lean_ctor_get(v___x_1040_, 1);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1044_ = v___x_1040_;
v_isShared_1045_ = v_isSharedCheck_1055_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_snd_1042_);
lean_inc(v_fst_1041_);
lean_dec(v___x_1040_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1055_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
size_t v_sz_1046_; size_t v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v_sz_1046_ = lean_array_size(v_xs_1025_);
v___x_1047_ = ((size_t)0ULL);
v___x_1048_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(v_fst_1032_, v_sz_1046_, v___x_1047_, v_xs_1025_);
lean_dec(v_fst_1032_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 3, v_fst_1041_);
lean_ctor_set(v___x_1029_, 2, v_fst_1035_);
lean_ctor_set(v___x_1029_, 1, v___x_1048_);
lean_ctor_set(v___x_1029_, 0, v_snd_1036_);
v___x_1050_ = v___x_1029_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_snd_1036_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1054_, 2, v_fst_1035_);
lean_ctor_set(v_reuseFailAlloc_1054_, 3, v_fst_1041_);
v___x_1050_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1052_; 
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1050_);
v___x_1052_ = v___x_1044_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_snd_1042_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
}
case 2:
{
lean_object* v_x_1065_; lean_object* v_i_1066_; lean_object* v_y_1067_; lean_object* v_b_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1087_; 
v_x_1065_ = lean_ctor_get(v_x_996_, 0);
v_i_1066_ = lean_ctor_get(v_x_996_, 1);
v_y_1067_ = lean_ctor_get(v_x_996_, 2);
v_b_1068_ = lean_ctor_get(v_x_996_, 3);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1070_ = v_x_996_;
v_isShared_1071_ = v_isSharedCheck_1087_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_b_1068_);
lean_inc(v_y_1067_);
lean_inc(v_i_1066_);
lean_inc(v_x_1065_);
lean_dec(v_x_996_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1087_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v_fst_1075_; lean_object* v_snd_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1086_; 
v___x_1072_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1065_, v_a_997_);
lean_dec(v_x_1065_);
v___x_1073_ = l_Lean_IR_NormalizeIds_normArg(v_y_1067_, v_a_997_);
v___x_1074_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1068_, v_a_997_, v_a_998_);
v_fst_1075_ = lean_ctor_get(v___x_1074_, 0);
v_snd_1076_ = lean_ctor_get(v___x_1074_, 1);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1078_ = v___x_1074_;
v_isShared_1079_ = v_isSharedCheck_1086_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_snd_1076_);
lean_inc(v_fst_1075_);
lean_dec(v___x_1074_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1086_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 3, v_fst_1075_);
lean_ctor_set(v___x_1070_, 2, v___x_1073_);
lean_ctor_set(v___x_1070_, 0, v___x_1072_);
v___x_1081_ = v___x_1070_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_i_1066_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1085_, 3, v_fst_1075_);
v___x_1081_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1083_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1081_);
v___x_1083_ = v___x_1078_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_snd_1076_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
case 3:
{
lean_object* v_x_1088_; lean_object* v_cidx_1089_; lean_object* v_b_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1108_; 
v_x_1088_ = lean_ctor_get(v_x_996_, 0);
v_cidx_1089_ = lean_ctor_get(v_x_996_, 1);
v_b_1090_ = lean_ctor_get(v_x_996_, 2);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1092_ = v_x_996_;
v_isShared_1093_ = v_isSharedCheck_1108_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_b_1090_);
lean_inc(v_cidx_1089_);
lean_inc(v_x_1088_);
lean_dec(v_x_996_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1108_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v_fst_1096_; lean_object* v_snd_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1107_; 
v___x_1094_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1088_, v_a_997_);
lean_dec(v_x_1088_);
v___x_1095_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1090_, v_a_997_, v_a_998_);
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
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 2, v_fst_1096_);
lean_ctor_set(v___x_1092_, 0, v___x_1094_);
v___x_1102_ = v___x_1092_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_cidx_1089_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v_fst_1096_);
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
case 4:
{
lean_object* v_x_1109_; lean_object* v_i_1110_; lean_object* v_y_1111_; lean_object* v_b_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1131_; 
v_x_1109_ = lean_ctor_get(v_x_996_, 0);
v_i_1110_ = lean_ctor_get(v_x_996_, 1);
v_y_1111_ = lean_ctor_get(v_x_996_, 2);
v_b_1112_ = lean_ctor_get(v_x_996_, 3);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1114_ = v_x_996_;
v_isShared_1115_ = v_isSharedCheck_1131_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_b_1112_);
lean_inc(v_y_1111_);
lean_inc(v_i_1110_);
lean_inc(v_x_1109_);
lean_dec(v_x_996_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1131_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v_fst_1119_; lean_object* v_snd_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1130_; 
v___x_1116_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1109_, v_a_997_);
lean_dec(v_x_1109_);
v___x_1117_ = l_Lean_IR_NormalizeIds_normIndex(v_y_1111_, v_a_997_);
lean_dec(v_y_1111_);
v___x_1118_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1112_, v_a_997_, v_a_998_);
v_fst_1119_ = lean_ctor_get(v___x_1118_, 0);
v_snd_1120_ = lean_ctor_get(v___x_1118_, 1);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1122_ = v___x_1118_;
v_isShared_1123_ = v_isSharedCheck_1130_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_snd_1120_);
lean_inc(v_fst_1119_);
lean_dec(v___x_1118_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1130_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 3, v_fst_1119_);
lean_ctor_set(v___x_1114_, 2, v___x_1117_);
lean_ctor_set(v___x_1114_, 0, v___x_1116_);
v___x_1125_ = v___x_1114_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_i_1110_);
lean_ctor_set(v_reuseFailAlloc_1129_, 2, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1129_, 3, v_fst_1119_);
v___x_1125_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
lean_object* v___x_1127_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1125_);
v___x_1127_ = v___x_1122_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1125_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_snd_1120_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
case 5:
{
lean_object* v_x_1132_; lean_object* v_i_1133_; lean_object* v_offset_1134_; lean_object* v_y_1135_; lean_object* v_ty_1136_; lean_object* v_b_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1156_; 
v_x_1132_ = lean_ctor_get(v_x_996_, 0);
v_i_1133_ = lean_ctor_get(v_x_996_, 1);
v_offset_1134_ = lean_ctor_get(v_x_996_, 2);
v_y_1135_ = lean_ctor_get(v_x_996_, 3);
v_ty_1136_ = lean_ctor_get(v_x_996_, 4);
v_b_1137_ = lean_ctor_get(v_x_996_, 5);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1139_ = v_x_996_;
v_isShared_1140_ = v_isSharedCheck_1156_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_b_1137_);
lean_inc(v_ty_1136_);
lean_inc(v_y_1135_);
lean_inc(v_offset_1134_);
lean_inc(v_i_1133_);
lean_inc(v_x_1132_);
lean_dec(v_x_996_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1156_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v_fst_1144_; lean_object* v_snd_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1155_; 
v___x_1141_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1132_, v_a_997_);
lean_dec(v_x_1132_);
v___x_1142_ = l_Lean_IR_NormalizeIds_normIndex(v_y_1135_, v_a_997_);
lean_dec(v_y_1135_);
v___x_1143_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1137_, v_a_997_, v_a_998_);
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
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 5, v_fst_1144_);
lean_ctor_set(v___x_1139_, 3, v___x_1142_);
lean_ctor_set(v___x_1139_, 0, v___x_1141_);
v___x_1150_ = v___x_1139_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_i_1133_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_offset_1134_);
lean_ctor_set(v_reuseFailAlloc_1154_, 3, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1154_, 4, v_ty_1136_);
lean_ctor_set(v_reuseFailAlloc_1154_, 5, v_fst_1144_);
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
case 6:
{
lean_object* v_x_1157_; lean_object* v_n_1158_; uint8_t v_c_1159_; uint8_t v_persistent_1160_; lean_object* v_b_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1179_; 
v_x_1157_ = lean_ctor_get(v_x_996_, 0);
v_n_1158_ = lean_ctor_get(v_x_996_, 1);
v_c_1159_ = lean_ctor_get_uint8(v_x_996_, sizeof(void*)*3);
v_persistent_1160_ = lean_ctor_get_uint8(v_x_996_, sizeof(void*)*3 + 1);
v_b_1161_ = lean_ctor_get(v_x_996_, 2);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1163_ = v_x_996_;
v_isShared_1164_ = v_isSharedCheck_1179_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_b_1161_);
lean_inc(v_n_1158_);
lean_inc(v_x_1157_);
lean_dec(v_x_996_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1179_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v_fst_1167_; lean_object* v_snd_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1178_; 
v___x_1165_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1157_, v_a_997_);
lean_dec(v_x_1157_);
v___x_1166_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1161_, v_a_997_, v_a_998_);
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
v_reuseFailAlloc_1177_ = lean_alloc_ctor(6, 3, 2);
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
case 7:
{
lean_object* v_x_1180_; lean_object* v_n_1181_; uint8_t v_c_1182_; uint8_t v_persistent_1183_; lean_object* v_b_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1202_; 
v_x_1180_ = lean_ctor_get(v_x_996_, 0);
v_n_1181_ = lean_ctor_get(v_x_996_, 1);
v_c_1182_ = lean_ctor_get_uint8(v_x_996_, sizeof(void*)*3);
v_persistent_1183_ = lean_ctor_get_uint8(v_x_996_, sizeof(void*)*3 + 1);
v_b_1184_ = lean_ctor_get(v_x_996_, 2);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1186_ = v_x_996_;
v_isShared_1187_ = v_isSharedCheck_1202_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_b_1184_);
lean_inc(v_n_1181_);
lean_inc(v_x_1180_);
lean_dec(v_x_996_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1202_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v_fst_1190_; lean_object* v_snd_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1201_; 
v___x_1188_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1180_, v_a_997_);
lean_dec(v_x_1180_);
v___x_1189_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1184_, v_a_997_, v_a_998_);
v_fst_1190_ = lean_ctor_get(v___x_1189_, 0);
v_snd_1191_ = lean_ctor_get(v___x_1189_, 1);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1193_ = v___x_1189_;
v_isShared_1194_ = v_isSharedCheck_1201_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_snd_1191_);
lean_inc(v_fst_1190_);
lean_dec(v___x_1189_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1201_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 2, v_fst_1190_);
lean_ctor_set(v___x_1186_, 0, v___x_1188_);
v___x_1196_ = v___x_1186_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_n_1181_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v_fst_1190_);
lean_ctor_set_uint8(v_reuseFailAlloc_1200_, sizeof(void*)*3, v_c_1182_);
lean_ctor_set_uint8(v_reuseFailAlloc_1200_, sizeof(void*)*3 + 1, v_persistent_1183_);
v___x_1196_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1196_);
v___x_1198_ = v___x_1193_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_snd_1191_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
case 8:
{
lean_object* v_x_1203_; lean_object* v_b_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1222_; 
v_x_1203_ = lean_ctor_get(v_x_996_, 0);
v_b_1204_ = lean_ctor_get(v_x_996_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1206_ = v_x_996_;
v_isShared_1207_ = v_isSharedCheck_1222_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_b_1204_);
lean_inc(v_x_1203_);
lean_dec(v_x_996_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1222_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_fst_1210_; lean_object* v_snd_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1221_; 
v___x_1208_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1203_, v_a_997_);
lean_dec(v_x_1203_);
v___x_1209_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1204_, v_a_997_, v_a_998_);
v_fst_1210_ = lean_ctor_get(v___x_1209_, 0);
v_snd_1211_ = lean_ctor_get(v___x_1209_, 1);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1213_ = v___x_1209_;
v_isShared_1214_ = v_isSharedCheck_1221_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_snd_1211_);
lean_inc(v_fst_1210_);
lean_dec(v___x_1209_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1221_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 1, v_fst_1210_);
lean_ctor_set(v___x_1206_, 0, v___x_1208_);
v___x_1216_ = v___x_1206_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_fst_1210_);
v___x_1216_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1218_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1216_);
v___x_1218_ = v___x_1213_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_snd_1211_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
case 9:
{
lean_object* v_tid_1223_; lean_object* v_x_1224_; lean_object* v_xType_1225_; lean_object* v_cs_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1246_; 
v_tid_1223_ = lean_ctor_get(v_x_996_, 0);
v_x_1224_ = lean_ctor_get(v_x_996_, 1);
v_xType_1225_ = lean_ctor_get(v_x_996_, 2);
v_cs_1226_ = lean_ctor_get(v_x_996_, 3);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1228_ = v_x_996_;
v_isShared_1229_ = v_isSharedCheck_1246_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_cs_1226_);
lean_inc(v_xType_1225_);
lean_inc(v_x_1224_);
lean_inc(v_tid_1223_);
lean_dec(v_x_996_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1246_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; size_t v_sz_1231_; size_t v___x_1232_; lean_object* v___x_1233_; lean_object* v_fst_1234_; lean_object* v_snd_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1245_; 
v___x_1230_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1224_, v_a_997_);
lean_dec(v_x_1224_);
v_sz_1231_ = lean_array_size(v_cs_1226_);
v___x_1232_ = ((size_t)0ULL);
v___x_1233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(v_sz_1231_, v___x_1232_, v_cs_1226_, v_a_997_, v_a_998_);
v_fst_1234_ = lean_ctor_get(v___x_1233_, 0);
v_snd_1235_ = lean_ctor_get(v___x_1233_, 1);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1237_ = v___x_1233_;
v_isShared_1238_ = v_isSharedCheck_1245_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_snd_1235_);
lean_inc(v_fst_1234_);
lean_dec(v___x_1233_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1245_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 3, v_fst_1234_);
lean_ctor_set(v___x_1228_, 1, v___x_1230_);
v___x_1240_ = v___x_1228_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_tid_1223_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v___x_1230_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v_xType_1225_);
lean_ctor_set(v_reuseFailAlloc_1244_, 3, v_fst_1234_);
v___x_1240_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
lean_object* v___x_1242_; 
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v___x_1240_);
v___x_1242_ = v___x_1237_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_snd_1235_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
}
case 10:
{
lean_object* v_x_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1256_; 
v_x_1247_ = lean_ctor_get(v_x_996_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1249_ = v_x_996_;
v_isShared_1250_ = v_isSharedCheck_1256_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_x_1247_);
lean_dec(v_x_996_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1256_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1251_ = l_Lean_IR_NormalizeIds_normArg(v_x_1247_, v_a_997_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1251_);
v___x_1253_ = v___x_1249_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
lean_ctor_set(v___x_1254_, 1, v_a_998_);
return v___x_1254_;
}
}
}
case 11:
{
lean_object* v_j_1257_; lean_object* v_ys_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1268_; 
v_j_1257_ = lean_ctor_get(v_x_996_, 0);
v_ys_1258_ = lean_ctor_get(v_x_996_, 1);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1260_ = v_x_996_;
v_isShared_1261_ = v_isSharedCheck_1268_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_ys_1258_);
lean_inc(v_j_1257_);
lean_dec(v_x_996_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1268_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1262_ = l_Lean_IR_NormalizeIds_normIndex(v_j_1257_, v_a_997_);
lean_dec(v_j_1257_);
v___x_1263_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_1258_, v_a_997_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 1, v___x_1263_);
lean_ctor_set(v___x_1260_, 0, v___x_1262_);
v___x_1265_ = v___x_1260_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1262_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set(v___x_1266_, 1, v_a_998_);
return v___x_1266_;
}
}
}
default: 
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1269_, 0, v_x_996_);
lean_ctor_set(v___x_1269_, 1, v_a_998_);
return v___x_1269_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(size_t v_sz_1270_, size_t v_i_1271_, lean_object* v_bs_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
uint8_t v___x_1275_; 
v___x_1275_ = lean_usize_dec_lt(v_i_1271_, v_sz_1270_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v_bs_1272_);
lean_ctor_set(v___x_1276_, 1, v___y_1274_);
return v___x_1276_;
}
else
{
lean_object* v_v_1277_; lean_object* v___x_1278_; lean_object* v_bs_x27_1279_; lean_object* v_fst_1281_; lean_object* v_snd_1282_; 
v_v_1277_ = lean_array_uget(v_bs_1272_, v_i_1271_);
v___x_1278_ = lean_unsigned_to_nat(0u);
v_bs_x27_1279_ = lean_array_uset(v_bs_1272_, v_i_1271_, v___x_1278_);
if (lean_obj_tag(v_v_1277_) == 0)
{
lean_object* v_info_1287_; lean_object* v_b_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1298_; 
v_info_1287_ = lean_ctor_get(v_v_1277_, 0);
v_b_1288_ = lean_ctor_get(v_v_1277_, 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_v_1277_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1290_ = v_v_1277_;
v_isShared_1291_ = v_isSharedCheck_1298_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_b_1288_);
lean_inc(v_info_1287_);
lean_dec(v_v_1277_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1298_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; lean_object* v_fst_1293_; lean_object* v_snd_1294_; lean_object* v___x_1296_; 
v___x_1292_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1288_, v___y_1273_, v___y_1274_);
v_fst_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_fst_1293_);
v_snd_1294_ = lean_ctor_get(v___x_1292_, 1);
lean_inc(v_snd_1294_);
lean_dec_ref(v___x_1292_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 1, v_fst_1293_);
v___x_1296_ = v___x_1290_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_info_1287_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_fst_1293_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
v_fst_1281_ = v___x_1296_;
v_snd_1282_ = v_snd_1294_;
goto v___jp_1280_;
}
}
}
else
{
lean_object* v_b_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1309_; 
v_b_1299_ = lean_ctor_get(v_v_1277_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_v_1277_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1301_ = v_v_1277_;
v_isShared_1302_ = v_isSharedCheck_1309_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_b_1299_);
lean_dec(v_v_1277_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1309_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v_fst_1304_; lean_object* v_snd_1305_; lean_object* v___x_1307_; 
v___x_1303_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1299_, v___y_1273_, v___y_1274_);
v_fst_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_fst_1304_);
v_snd_1305_ = lean_ctor_get(v___x_1303_, 1);
lean_inc(v_snd_1305_);
lean_dec_ref(v___x_1303_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v_fst_1304_);
v___x_1307_ = v___x_1301_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_fst_1304_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
v_fst_1281_ = v___x_1307_;
v_snd_1282_ = v_snd_1305_;
goto v___jp_1280_;
}
}
}
v___jp_1280_:
{
size_t v___x_1283_; size_t v___x_1284_; lean_object* v___x_1285_; 
v___x_1283_ = ((size_t)1ULL);
v___x_1284_ = lean_usize_add(v_i_1271_, v___x_1283_);
v___x_1285_ = lean_array_uset(v_bs_x27_1279_, v_i_1271_, v_fst_1281_);
v_i_1271_ = v___x_1284_;
v_bs_1272_ = v___x_1285_;
v___y_1274_ = v_snd_1282_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2___boxed(lean_object* v_sz_1310_, lean_object* v_i_1311_, lean_object* v_bs_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
size_t v_sz_boxed_1315_; size_t v_i_boxed_1316_; lean_object* v_res_1317_; 
v_sz_boxed_1315_ = lean_unbox_usize(v_sz_1310_);
lean_dec(v_sz_1310_);
v_i_boxed_1316_ = lean_unbox_usize(v_i_1311_);
lean_dec(v_i_1311_);
v_res_1317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(v_sz_boxed_1315_, v_i_boxed_1316_, v_bs_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1313_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normFnBody___boxed(lean_object* v_x_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_IR_NormalizeIds_normFnBody(v_x_1318_, v_a_1319_, v_a_1320_);
lean_dec(v_a_1319_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normDecl(lean_object* v_d_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
if (lean_obj_tag(v_d_1322_) == 0)
{
lean_object* v_xs_1325_; lean_object* v_body_1326_; lean_object* v_fst_1328_; lean_object* v_snd_1329_; lean_object* v___x_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v_xs_1325_ = lean_ctor_get(v_d_1322_, 1);
v_body_1326_ = lean_ctor_get(v_d_1322_, 3);
v___x_1341_ = lean_unsigned_to_nat(0u);
v___x_1342_ = lean_array_get_size(v_xs_1325_);
v___x_1343_ = lean_nat_dec_lt(v___x_1341_, v___x_1342_);
if (v___x_1343_ == 0)
{
lean_inc(v_a_1323_);
v_fst_1328_ = v_a_1323_;
v_snd_1329_ = v_a_1324_;
goto v___jp_1327_;
}
else
{
size_t v___x_1344_; size_t v___x_1345_; lean_object* v___x_1346_; lean_object* v_fst_1347_; lean_object* v_snd_1348_; 
v___x_1344_ = ((size_t)0ULL);
v___x_1345_ = lean_usize_of_nat(v___x_1342_);
lean_inc(v_a_1323_);
v___x_1346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_1325_, v___x_1344_, v___x_1345_, v_a_1323_, v_a_1324_);
v_fst_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_fst_1347_);
v_snd_1348_ = lean_ctor_get(v___x_1346_, 1);
lean_inc(v_snd_1348_);
lean_dec_ref(v___x_1346_);
v_fst_1328_ = v_fst_1347_;
v_snd_1329_ = v_snd_1348_;
goto v___jp_1327_;
}
v___jp_1327_:
{
lean_object* v___x_1330_; lean_object* v_fst_1331_; lean_object* v_snd_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1340_; 
lean_inc(v_body_1326_);
v___x_1330_ = l_Lean_IR_NormalizeIds_normFnBody(v_body_1326_, v_fst_1328_, v_snd_1329_);
lean_dec(v_fst_1328_);
v_fst_1331_ = lean_ctor_get(v___x_1330_, 0);
v_snd_1332_ = lean_ctor_get(v___x_1330_, 1);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1334_ = v___x_1330_;
v_isShared_1335_ = v_isSharedCheck_1340_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_snd_1332_);
lean_inc(v_fst_1331_);
lean_dec(v___x_1330_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1340_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1336_ = l_Lean_IR_Decl_updateBody_x21(v_d_1322_, v_fst_1331_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1336_);
v___x_1338_ = v___x_1334_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_snd_1332_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
else
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1349_, 0, v_d_1322_);
lean_ctor_set(v___x_1349_, 1, v_a_1324_);
return v___x_1349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normDecl___boxed(lean_object* v_d_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_IR_NormalizeIds_normDecl(v_d_1350_, v_a_1351_, v_a_1352_);
lean_dec(v_a_1351_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_normalizeIds(lean_object* v_d_1354_){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v_fst_1358_; 
v___x_1355_ = lean_box(1);
v___x_1356_ = lean_unsigned_to_nat(1u);
v___x_1357_ = l_Lean_IR_NormalizeIds_normDecl(v_d_1354_, v___x_1355_, v___x_1356_);
v_fst_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_fst_1358_);
lean_dec_ref(v___x_1357_);
return v_fst_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArg(lean_object* v_f_1359_, lean_object* v_x_1360_){
_start:
{
if (lean_obj_tag(v_x_1360_) == 0)
{
lean_object* v_id_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1369_; 
v_id_1361_ = lean_ctor_get(v_x_1360_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_x_1360_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1363_ = v_x_1360_;
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_id_1361_);
lean_dec(v_x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1365_ = lean_apply_1(v_f_1359_, v_id_1361_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1365_);
v___x_1367_ = v___x_1363_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
else
{
lean_dec_ref(v_f_1359_);
return v_x_1360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(lean_object* v_f_1370_, size_t v_sz_1371_, size_t v_i_1372_, lean_object* v_bs_1373_){
_start:
{
uint8_t v___x_1374_; 
v___x_1374_ = lean_usize_dec_lt(v_i_1372_, v_sz_1371_);
if (v___x_1374_ == 0)
{
lean_dec_ref(v_f_1370_);
return v_bs_1373_;
}
else
{
lean_object* v_v_1375_; lean_object* v___x_1376_; lean_object* v_bs_x27_1377_; lean_object* v___y_1379_; 
v_v_1375_ = lean_array_uget(v_bs_1373_, v_i_1372_);
v___x_1376_ = lean_unsigned_to_nat(0u);
v_bs_x27_1377_ = lean_array_uset(v_bs_1373_, v_i_1372_, v___x_1376_);
if (lean_obj_tag(v_v_1375_) == 0)
{
lean_object* v_id_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1392_; 
v_id_1384_ = lean_ctor_get(v_v_1375_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v_v_1375_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1386_ = v_v_1375_;
v_isShared_1387_ = v_isSharedCheck_1392_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_id_1384_);
lean_dec(v_v_1375_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1392_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
lean_inc_ref(v_f_1370_);
v___x_1388_ = lean_apply_1(v_f_1370_, v_id_1384_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1388_);
v___x_1390_ = v___x_1386_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
v___y_1379_ = v___x_1390_;
goto v___jp_1378_;
}
}
}
else
{
v___y_1379_ = v_v_1375_;
goto v___jp_1378_;
}
v___jp_1378_:
{
size_t v___x_1380_; size_t v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = ((size_t)1ULL);
v___x_1381_ = lean_usize_add(v_i_1372_, v___x_1380_);
v___x_1382_ = lean_array_uset(v_bs_x27_1377_, v_i_1372_, v___y_1379_);
v_i_1372_ = v___x_1381_;
v_bs_1373_ = v___x_1382_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0___boxed(lean_object* v_f_1393_, lean_object* v_sz_1394_, lean_object* v_i_1395_, lean_object* v_bs_1396_){
_start:
{
size_t v_sz_boxed_1397_; size_t v_i_boxed_1398_; lean_object* v_res_1399_; 
v_sz_boxed_1397_ = lean_unbox_usize(v_sz_1394_);
lean_dec(v_sz_1394_);
v_i_boxed_1398_ = lean_unbox_usize(v_i_1395_);
lean_dec(v_i_1395_);
v_res_1399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(v_f_1393_, v_sz_boxed_1397_, v_i_boxed_1398_, v_bs_1396_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArgs(lean_object* v_f_1400_, lean_object* v_as_1401_){
_start:
{
size_t v_sz_1402_; size_t v___x_1403_; lean_object* v___x_1404_; 
v_sz_1402_ = lean_array_size(v_as_1401_);
v___x_1403_ = ((size_t)0ULL);
v___x_1404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(v_f_1400_, v_sz_1402_, v___x_1403_, v_as_1401_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapExpr(lean_object* v_f_1405_, lean_object* v_x_1406_){
_start:
{
switch(lean_obj_tag(v_x_1406_))
{
case 0:
{
lean_object* v_i_1407_; lean_object* v_ys_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1416_; 
v_i_1407_ = lean_ctor_get(v_x_1406_, 0);
v_ys_1408_ = lean_ctor_get(v_x_1406_, 1);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_x_1406_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1410_ = v_x_1406_;
v_isShared_1411_ = v_isSharedCheck_1416_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_ys_1408_);
lean_inc(v_i_1407_);
lean_dec(v_x_1406_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1416_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = l_Lean_IR_MapVars_mapArgs(v_f_1405_, v_ys_1408_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 1, v___x_1412_);
v___x_1414_ = v___x_1410_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_i_1407_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
case 1:
{
lean_object* v_n_1417_; lean_object* v_x_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1426_; 
v_n_1417_ = lean_ctor_get(v_x_1406_, 0);
v_x_1418_ = lean_ctor_get(v_x_1406_, 1);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_x_1406_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1420_ = v_x_1406_;
v_isShared_1421_ = v_isSharedCheck_1426_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_x_1418_);
lean_inc(v_n_1417_);
lean_dec(v_x_1406_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1426_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1422_ = lean_apply_1(v_f_1405_, v_x_1418_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 1, v___x_1422_);
v___x_1424_ = v___x_1420_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_n_1417_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
case 2:
{
lean_object* v_x_1427_; lean_object* v_i_1428_; uint8_t v_updtHeader_1429_; lean_object* v_ys_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1439_; 
v_x_1427_ = lean_ctor_get(v_x_1406_, 0);
v_i_1428_ = lean_ctor_get(v_x_1406_, 1);
v_updtHeader_1429_ = lean_ctor_get_uint8(v_x_1406_, sizeof(void*)*3);
v_ys_1430_ = lean_ctor_get(v_x_1406_, 2);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_x_1406_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1432_ = v_x_1406_;
v_isShared_1433_ = v_isSharedCheck_1439_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_ys_1430_);
lean_inc(v_i_1428_);
lean_inc(v_x_1427_);
lean_dec(v_x_1406_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1439_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
lean_inc_ref(v_f_1405_);
v___x_1434_ = lean_apply_1(v_f_1405_, v_x_1427_);
v___x_1435_ = l_Lean_IR_MapVars_mapArgs(v_f_1405_, v_ys_1430_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 2, v___x_1435_);
lean_ctor_set(v___x_1432_, 0, v___x_1434_);
v___x_1437_ = v___x_1432_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_i_1428_);
lean_ctor_set(v_reuseFailAlloc_1438_, 2, v___x_1435_);
lean_ctor_set_uint8(v_reuseFailAlloc_1438_, sizeof(void*)*3, v_updtHeader_1429_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
case 3:
{
lean_object* v_i_1440_; lean_object* v_x_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1449_; 
v_i_1440_ = lean_ctor_get(v_x_1406_, 0);
v_x_1441_ = lean_ctor_get(v_x_1406_, 1);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_x_1406_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1443_ = v_x_1406_;
v_isShared_1444_ = v_isSharedCheck_1449_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_x_1441_);
lean_inc(v_i_1440_);
lean_dec(v_x_1406_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1449_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1445_; lean_object* v___x_1447_; 
v___x_1445_ = lean_apply_1(v_f_1405_, v_x_1441_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 1, v___x_1445_);
v___x_1447_ = v___x_1443_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_i_1440_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
case 4:
{
lean_object* v_i_1450_; lean_object* v_x_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1459_; 
v_i_1450_ = lean_ctor_get(v_x_1406_, 0);
v_x_1451_ = lean_ctor_get(v_x_1406_, 1);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_x_1406_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1453_ = v_x_1406_;
v_isShared_1454_ = v_isSharedCheck_1459_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_x_1451_);
lean_inc(v_i_1450_);
lean_dec(v_x_1406_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1459_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1455_ = lean_apply_1(v_f_1405_, v_x_1451_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 1, v___x_1455_);
v___x_1457_ = v___x_1453_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_i_1450_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
case 5:
{
lean_object* v_n_1460_; lean_object* v_offset_1461_; lean_object* v_x_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1470_; 
v_n_1460_ = lean_ctor_get(v_x_1406_, 0);
v_offset_1461_ = lean_ctor_get(v_x_1406_, 1);
v_x_1462_ = lean_ctor_get(v_x_1406_, 2);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_x_1406_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1464_ = v_x_1406_;
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_x_1462_);
lean_inc(v_offset_1461_);
lean_inc(v_n_1460_);
lean_dec(v_x_1406_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1466_ = lean_apply_1(v_f_1405_, v_x_1462_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 2, v___x_1466_);
v___x_1468_ = v___x_1464_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_n_1460_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_offset_1461_);
lean_ctor_set(v_reuseFailAlloc_1469_, 2, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
case 6:
{
lean_object* v_c_1471_; lean_object* v_ys_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1480_; 
v_c_1471_ = lean_ctor_get(v_x_1406_, 0);
v_ys_1472_ = lean_ctor_get(v_x_1406_, 1);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_x_1406_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1474_ = v_x_1406_;
v_isShared_1475_ = v_isSharedCheck_1480_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_ys_1472_);
lean_inc(v_c_1471_);
lean_dec(v_x_1406_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1480_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; lean_object* v___x_1478_; 
v___x_1476_ = l_Lean_IR_MapVars_mapArgs(v_f_1405_, v_ys_1472_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 1, v___x_1476_);
v___x_1478_ = v___x_1474_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_c_1471_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
case 7:
{
lean_object* v_c_1481_; lean_object* v_ys_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1490_; 
v_c_1481_ = lean_ctor_get(v_x_1406_, 0);
v_ys_1482_ = lean_ctor_get(v_x_1406_, 1);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_x_1406_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1484_ = v_x_1406_;
v_isShared_1485_ = v_isSharedCheck_1490_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_ys_1482_);
lean_inc(v_c_1481_);
lean_dec(v_x_1406_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1490_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1486_ = l_Lean_IR_MapVars_mapArgs(v_f_1405_, v_ys_1482_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 1, v___x_1486_);
v___x_1488_ = v___x_1484_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_c_1481_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
case 8:
{
lean_object* v_x_1491_; lean_object* v_ys_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1501_; 
v_x_1491_ = lean_ctor_get(v_x_1406_, 0);
v_ys_1492_ = lean_ctor_get(v_x_1406_, 1);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_x_1406_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1494_ = v_x_1406_;
v_isShared_1495_ = v_isSharedCheck_1501_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_ys_1492_);
lean_inc(v_x_1491_);
lean_dec(v_x_1406_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1501_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1499_; 
lean_inc_ref(v_f_1405_);
v___x_1496_ = lean_apply_1(v_f_1405_, v_x_1491_);
v___x_1497_ = l_Lean_IR_MapVars_mapArgs(v_f_1405_, v_ys_1492_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v___x_1497_);
lean_ctor_set(v___x_1494_, 0, v___x_1496_);
v___x_1499_ = v___x_1494_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
case 9:
{
lean_object* v_ty_1502_; lean_object* v_x_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1511_; 
v_ty_1502_ = lean_ctor_get(v_x_1406_, 0);
v_x_1503_ = lean_ctor_get(v_x_1406_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_x_1406_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1505_ = v_x_1406_;
v_isShared_1506_ = v_isSharedCheck_1511_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_x_1503_);
lean_inc(v_ty_1502_);
lean_dec(v_x_1406_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1511_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1507_ = lean_apply_1(v_f_1405_, v_x_1503_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 1, v___x_1507_);
v___x_1509_ = v___x_1505_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_ty_1502_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
case 10:
{
lean_object* v_x_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1520_; 
v_x_1512_ = lean_ctor_get(v_x_1406_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_x_1406_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1514_ = v_x_1406_;
v_isShared_1515_ = v_isSharedCheck_1520_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_x_1512_);
lean_dec(v_x_1406_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1520_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1516_ = lean_apply_1(v_f_1405_, v_x_1512_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 0, v___x_1516_);
v___x_1518_ = v___x_1514_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
case 11:
{
lean_dec_ref(v_f_1405_);
return v_x_1406_;
}
default: 
{
lean_object* v_x_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1529_; 
v_x_1521_ = lean_ctor_get(v_x_1406_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_x_1406_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1523_ = v_x_1406_;
v_isShared_1524_ = v_isSharedCheck_1529_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_x_1521_);
lean_dec(v_x_1406_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1529_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1525_; lean_object* v___x_1527_; 
v___x_1525_ = lean_apply_1(v_f_1405_, v_x_1521_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1525_);
v___x_1527_ = v___x_1523_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapFnBody(lean_object* v_f_1530_, lean_object* v_x_1531_){
_start:
{
switch(lean_obj_tag(v_x_1531_))
{
case 0:
{
lean_object* v_x_1532_; lean_object* v_ty_1533_; lean_object* v_e_1534_; lean_object* v_b_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1544_; 
v_x_1532_ = lean_ctor_get(v_x_1531_, 0);
v_ty_1533_ = lean_ctor_get(v_x_1531_, 1);
v_e_1534_ = lean_ctor_get(v_x_1531_, 2);
v_b_1535_ = lean_ctor_get(v_x_1531_, 3);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_x_1531_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1537_ = v_x_1531_;
v_isShared_1538_ = v_isSharedCheck_1544_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_b_1535_);
lean_inc(v_e_1534_);
lean_inc(v_ty_1533_);
lean_inc(v_x_1532_);
lean_dec(v_x_1531_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1544_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
lean_inc_ref(v_f_1530_);
v___x_1539_ = l_Lean_IR_MapVars_mapExpr(v_f_1530_, v_e_1534_);
v___x_1540_ = l_Lean_IR_MapVars_mapFnBody(v_f_1530_, v_b_1535_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 3, v___x_1540_);
lean_ctor_set(v___x_1537_, 2, v___x_1539_);
v___x_1542_ = v___x_1537_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_x_1532_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_ty_1533_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
case 1:
{
lean_object* v_j_1545_; lean_object* v_xs_1546_; lean_object* v_v_1547_; lean_object* v_b_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1557_; 
v_j_1545_ = lean_ctor_get(v_x_1531_, 0);
v_xs_1546_ = lean_ctor_get(v_x_1531_, 1);
v_v_1547_ = lean_ctor_get(v_x_1531_, 2);
v_b_1548_ = lean_ctor_get(v_x_1531_, 3);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_x_1531_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1550_ = v_x_1531_;
v_isShared_1551_ = v_isSharedCheck_1557_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_b_1548_);
lean_inc(v_v_1547_);
lean_inc(v_xs_1546_);
lean_inc(v_j_1545_);
lean_dec(v_x_1531_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1557_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; 
lean_inc_ref(v_f_1530_);
v___x_1552_ = l_Lean_IR_MapVars_mapFnBody(v_f_1530_, v_v_1547_);
v___x_1553_ = l_Lean_IR_MapVars_mapFnBody(v_f_1530_, v_b_1548_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 3, v___x_1553_);
lean_ctor_set(v___x_1550_, 2, v___x_1552_);
v___x_1555_ = v___x_1550_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_j_1545_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_xs_1546_);
lean_ctor_set(v_reuseFailAlloc_1556_, 2, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1556_, 3, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
case 2:
{
lean_object* v_x_1558_; lean_object* v_i_1559_; lean_object* v_y_1560_; lean_object* v_b_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1581_; 
v_x_1558_ = lean_ctor_get(v_x_1531_, 0);
v_i_1559_ = lean_ctor_get(v_x_1531_, 1);
v_y_1560_ = lean_ctor_get(v_x_1531_, 2);
v_b_1561_ = lean_ctor_get(v_x_1531_, 3);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_x_1531_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1563_ = v_x_1531_;
v_isShared_1564_ = v_isSharedCheck_1581_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_b_1561_);
lean_inc(v_y_1560_);
lean_inc(v_i_1559_);
lean_inc(v_x_1558_);
lean_dec(v_x_1531_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1581_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1565_; lean_object* v___y_1567_; 
lean_inc_ref(v_f_1530_);
v___x_1565_ = lean_apply_1(v_f_1530_, v_x_1558_);
if (lean_obj_tag(v_y_1560_) == 0)
{
lean_object* v_id_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1580_; 
v_id_1572_ = lean_ctor_get(v_y_1560_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_y_1560_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1574_ = v_y_1560_;
v_isShared_1575_ = v_isSharedCheck_1580_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_id_1572_);
lean_dec(v_y_1560_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1580_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; lean_object* v___x_1578_; 
lean_inc_ref(v_f_1530_);
v___x_1576_ = lean_apply_1(v_f_1530_, v_id_1572_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v___x_1576_);
v___x_1578_ = v___x_1574_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
v___y_1567_ = v___x_1578_;
goto v___jp_1566_;
}
}
}
else
{
v___y_1567_ = v_y_1560_;
goto v___jp_1566_;
}
v___jp_1566_:
{
lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1568_ = l_Lean_IR_MapVars_mapFnBody(v_f_1530_, v_b_1561_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 3, v___x_1568_);
lean_ctor_set(v___x_1563_, 2, v___y_1567_);
lean_ctor_set(v___x_1563_, 0, v___x_1565_);
v___x_1570_ = v___x_1563_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_i_1559_);
lean_ctor_set(v_reuseFailAlloc_1571_, 2, v___y_1567_);
lean_ctor_set(v_reuseFailAlloc_1571_, 3, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
case 3:
{
lean_object* v_x_1582_; lean_object* v_cidx_1583_; lean_object* v_b_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1593_; 
v_x_1582_ = lean_ctor_get(v_x_1531_, 0);
v_cidx_1583_ = lean_ctor_get(v_x_1531_, 1);
v_b_1584_ = lean_ctor_get(v_x_1531_, 2);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_x_1531_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1586_ = v_x_1531_;
v_isShared_1587_ = v_isSharedCheck_1593_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_b_1584_);
lean_inc(v_cidx_1583_);
lean_inc(v_x_1582_);
lean_dec(v_x_1531_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1593_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
lean_inc_ref(v_f_1530_);
v___x_1588_ = lean_apply_1(v_f_1530_, v_x_1582_);
v___x_1589_ = l_Lean_IR_MapVars_mapFnBody(v_f_1530_, v_b_1584_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 2, v___x_1589_);
lean_ctor_set(v___x_1586_, 0, v___x_1588_);
v___x_1591_ = v___x_1586_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_cidx_1583_);
lean_ctor_set(v_reuseFailAlloc_1592_, 2, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
case 4:
{
lean_object* v_x_1594_; lean_object* v_i_1595_; lean_object* v_y_1596_; lean_object* v_b_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1607_; 
v_x_1594_ = lean_ctor_get(v_x_1531_, 0);
v_i_1595_ = lean_ctor_get(v_x_1531_, 1);
v_y_1596_ = lean_ctor_get(v_x_1531_, 2);
v_b_1597_ = lean_ctor_get(v_x_1531_, 3);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_x_1531_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1599_ = v_x_1531_;
v_isShared_1600_ = v_isSharedCheck_1607_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_b_1597_);
lean_inc(v_y_1596_);
lean_inc(v_i_1595_);
lean_inc(v_x_1594_);
lean_dec(v_x_1531_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1607_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
lean_inc_ref_n(v_f_1530_, 2);
v___x_1601_ = lean_apply_1(v_f_1530_, v_x_1594_);
v___x_1602_ = lean_apply_1(v_f_1530_, v_y_1596_);
v___x_1603_ = l_Lean_IR_MapVars_mapFnBody(v_f_1530_, v_b_1597_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 3, v___x_1603_);
lean_ctor_set(v___x_1599_, 2, v___x_1602_);
lean_ctor_set(v___x_1599_, 0, v___x_1601_);
v___x_1605_ = v___x_1599_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1601_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_i_1595_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1606_, 3, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
case 5:
{
lean_object* v_x_1608_; lean_object* v_i_1609_; lean_object* v_offset_1610_; lean_object* v_y_1611_; lean_object* v_ty_1612_; lean_object* v_b_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1623_; 
v_x_1608_ = lean_ctor_get(v_x_1531_, 0);
v_i_1609_ = lean_ctor_get(v_x_1531_, 1);
v_offset_1610_ = lean_ctor_get(v_x_1531_, 2);
v_y_1611_ = lean_ctor_get(v_x_1531_, 3);
v_ty_1612_ = lean_ctor_get(v_x_1531_, 4);
v_b_1613_ = lean_ctor_get(v_x_1531_, 5);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_x_1531_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1615_ = v_x_1531_;
v_isShared_1616_ = v_isSharedCheck_1623_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_b_1613_);
lean_inc(v_ty_1612_);
lean_inc(v_y_1611_);
lean_inc(v_offset_1610_);
lean_inc(v_i_1609_);
lean_inc(v_x_1608_);
lean_dec(v_x_1531_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1623_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
lean_inc_ref_n(v_f_1530_, 2);
v___x_1617_ = lean_apply_1(v_f_1530_, v_x_1608_);
v___x_1618_ = lean_apply_1(v_f_1530_, v_y_1611_);
v___x_1619_ = l_Lean_IR_MapVars_mapFnBody(v_f_1530_, v_b_1613_);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 5, v___x_1619_);
lean_ctor_set(v___x_1615_, 3, v___x_1618_);
lean_ctor_set(v___x_1615_, 0, v___x_1617_);
v___x_1621_ = v___x_1615_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1617_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_i_1609_);
lean_ctor_set(v_reuseFailAlloc_1622_, 2, v_offset_1610_);
lean_ctor_set(v_reuseFailAlloc_1622_, 3, v___x_1618_);
lean_ctor_set(v_reuseFailAlloc_1622_, 4, v_ty_1612_);
lean_ctor_set(v_reuseFailAlloc_1622_, 5, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
case 6:
{
lean_object* v_x_1624_; lean_object* v_n_1625_; uint8_t v_c_1626_; uint8_t v_persistent_1627_; lean_object* v_b_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1637_; 
v_x_1624_ = lean_ctor_get(v_x_1531_, 0);
v_n_1625_ = lean_ctor_get(v_x_1531_, 1);
v_c_1626_ = lean_ctor_get_uint8(v_x_1531_, sizeof(void*)*3);
v_persistent_1627_ = lean_ctor_get_uint8(v_x_1531_, sizeof(void*)*3 + 1);
v_b_1628_ = lean_ctor_get(v_x_1531_, 2);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_x_1531_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1630_ = v_x_1531_;
v_isShared_1631_ = v_isSharedCheck_1637_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_b_1628_);
lean_inc(v_n_1625_);
lean_inc(v_x_1624_);
lean_dec(v_x_1531_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1637_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; 
lean_inc_ref(v_f_1530_);
v___x_1632_ = lean_apply_1(v_f_1530_, v_x_1624_);
v___x_1633_ = l_Lean_IR_MapVars_mapFnBody(v_f_1530_, v_b_1628_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 2, v___x_1633_);
lean_ctor_set(v___x_1630_, 0, v___x_1632_);
v___x_1635_ = v___x_1630_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_n_1625_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v___x_1633_);
lean_ctor_set_uint8(v_reuseFailAlloc_1636_, sizeof(void*)*3, v_c_1626_);
lean_ctor_set_uint8(v_reuseFailAlloc_1636_, sizeof(void*)*3 + 1, v_persistent_1627_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
case 7:
{
lean_object* v_x_1638_; lean_object* v_n_1639_; uint8_t v_c_1640_; uint8_t v_persistent_1641_; lean_object* v_b_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1651_; 
v_x_1638_ = lean_ctor_get(v_x_1531_, 0);
v_n_1639_ = lean_ctor_get(v_x_1531_, 1);
v_c_1640_ = lean_ctor_get_uint8(v_x_1531_, sizeof(void*)*3);
v_persistent_1641_ = lean_ctor_get_uint8(v_x_1531_, sizeof(void*)*3 + 1);
v_b_1642_ = lean_ctor_get(v_x_1531_, 2);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_x_1531_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1644_ = v_x_1531_;
v_isShared_1645_ = v_isSharedCheck_1651_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_b_1642_);
lean_inc(v_n_1639_);
lean_inc(v_x_1638_);
lean_dec(v_x_1531_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1651_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1649_; 
lean_inc_ref(v_f_1530_);
v___x_1646_ = lean_apply_1(v_f_1530_, v_x_1638_);
v___x_1647_ = l_Lean_IR_MapVars_mapFnBody(v_f_1530_, v_b_1642_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 2, v___x_1647_);
lean_ctor_set(v___x_1644_, 0, v___x_1646_);
v___x_1649_ = v___x_1644_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1646_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_n_1639_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v___x_1647_);
lean_ctor_set_uint8(v_reuseFailAlloc_1650_, sizeof(void*)*3, v_c_1640_);
lean_ctor_set_uint8(v_reuseFailAlloc_1650_, sizeof(void*)*3 + 1, v_persistent_1641_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
case 8:
{
lean_object* v_x_1652_; lean_object* v_b_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1662_; 
v_x_1652_ = lean_ctor_get(v_x_1531_, 0);
v_b_1653_ = lean_ctor_get(v_x_1531_, 1);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_x_1531_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1655_ = v_x_1531_;
v_isShared_1656_ = v_isSharedCheck_1662_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_b_1653_);
lean_inc(v_x_1652_);
lean_dec(v_x_1531_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1662_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1660_; 
lean_inc_ref(v_f_1530_);
v___x_1657_ = lean_apply_1(v_f_1530_, v_x_1652_);
v___x_1658_ = l_Lean_IR_MapVars_mapFnBody(v_f_1530_, v_b_1653_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 1, v___x_1658_);
lean_ctor_set(v___x_1655_, 0, v___x_1657_);
v___x_1660_ = v___x_1655_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
case 9:
{
lean_object* v_tid_1663_; lean_object* v_x_1664_; lean_object* v_xType_1665_; lean_object* v_cs_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1677_; 
v_tid_1663_ = lean_ctor_get(v_x_1531_, 0);
v_x_1664_ = lean_ctor_get(v_x_1531_, 1);
v_xType_1665_ = lean_ctor_get(v_x_1531_, 2);
v_cs_1666_ = lean_ctor_get(v_x_1531_, 3);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_x_1531_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1668_ = v_x_1531_;
v_isShared_1669_ = v_isSharedCheck_1677_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_cs_1666_);
lean_inc(v_xType_1665_);
lean_inc(v_x_1664_);
lean_inc(v_tid_1663_);
lean_dec(v_x_1531_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1677_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; size_t v_sz_1671_; size_t v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
lean_inc_ref(v_f_1530_);
v___x_1670_ = lean_apply_1(v_f_1530_, v_x_1664_);
v_sz_1671_ = lean_array_size(v_cs_1666_);
v___x_1672_ = ((size_t)0ULL);
v___x_1673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(v_f_1530_, v_sz_1671_, v___x_1672_, v_cs_1666_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 3, v___x_1673_);
lean_ctor_set(v___x_1668_, 1, v___x_1670_);
v___x_1675_ = v___x_1668_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_tid_1663_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v___x_1670_);
lean_ctor_set(v_reuseFailAlloc_1676_, 2, v_xType_1665_);
lean_ctor_set(v_reuseFailAlloc_1676_, 3, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
case 10:
{
lean_object* v_x_1678_; 
v_x_1678_ = lean_ctor_get(v_x_1531_, 0);
lean_inc(v_x_1678_);
if (lean_obj_tag(v_x_1678_) == 0)
{
lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1694_; 
v_isSharedCheck_1694_ = !lean_is_exclusive(v_x_1531_);
if (v_isSharedCheck_1694_ == 0)
{
lean_object* v_unused_1695_; 
v_unused_1695_ = lean_ctor_get(v_x_1531_, 0);
lean_dec(v_unused_1695_);
v___x_1680_ = v_x_1531_;
v_isShared_1681_ = v_isSharedCheck_1694_;
goto v_resetjp_1679_;
}
else
{
lean_dec(v_x_1531_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1694_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v_id_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1693_; 
v_id_1682_ = lean_ctor_get(v_x_1678_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_x_1678_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1684_ = v_x_1678_;
v_isShared_1685_ = v_isSharedCheck_1693_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_id_1682_);
lean_dec(v_x_1678_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1693_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1686_ = lean_apply_1(v_f_1530_, v_id_1682_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1686_);
v___x_1688_ = v___x_1684_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1690_; 
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1688_);
v___x_1690_ = v___x_1680_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_1530_);
return v_x_1531_;
}
}
case 11:
{
lean_object* v_j_1696_; lean_object* v_ys_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1705_; 
v_j_1696_ = lean_ctor_get(v_x_1531_, 0);
v_ys_1697_ = lean_ctor_get(v_x_1531_, 1);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_x_1531_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1699_ = v_x_1531_;
v_isShared_1700_ = v_isSharedCheck_1705_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_ys_1697_);
lean_inc(v_j_1696_);
lean_dec(v_x_1531_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1705_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1701_; lean_object* v___x_1703_; 
v___x_1701_ = l_Lean_IR_MapVars_mapArgs(v_f_1530_, v_ys_1697_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 1, v___x_1701_);
v___x_1703_ = v___x_1699_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_j_1696_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
default: 
{
lean_dec_ref(v_f_1530_);
return v_x_1531_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(lean_object* v_f_1706_, size_t v_sz_1707_, size_t v_i_1708_, lean_object* v_bs_1709_){
_start:
{
uint8_t v___x_1710_; 
v___x_1710_ = lean_usize_dec_lt(v_i_1708_, v_sz_1707_);
if (v___x_1710_ == 0)
{
lean_dec_ref(v_f_1706_);
return v_bs_1709_;
}
else
{
lean_object* v_v_1711_; lean_object* v___x_1712_; lean_object* v_bs_x27_1713_; lean_object* v___y_1715_; 
v_v_1711_ = lean_array_uget(v_bs_1709_, v_i_1708_);
v___x_1712_ = lean_unsigned_to_nat(0u);
v_bs_x27_1713_ = lean_array_uset(v_bs_1709_, v_i_1708_, v___x_1712_);
if (lean_obj_tag(v_v_1711_) == 0)
{
lean_object* v_info_1720_; lean_object* v_b_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1729_; 
v_info_1720_ = lean_ctor_get(v_v_1711_, 0);
v_b_1721_ = lean_ctor_get(v_v_1711_, 1);
v_isSharedCheck_1729_ = !lean_is_exclusive(v_v_1711_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1723_ = v_v_1711_;
v_isShared_1724_ = v_isSharedCheck_1729_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_b_1721_);
lean_inc(v_info_1720_);
lean_dec(v_v_1711_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1729_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1725_; lean_object* v___x_1727_; 
lean_inc_ref(v_f_1706_);
v___x_1725_ = l_Lean_IR_MapVars_mapFnBody(v_f_1706_, v_b_1721_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 1, v___x_1725_);
v___x_1727_ = v___x_1723_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_info_1720_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
v___y_1715_ = v___x_1727_;
goto v___jp_1714_;
}
}
}
else
{
lean_object* v_b_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1738_; 
v_b_1730_ = lean_ctor_get(v_v_1711_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_v_1711_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1732_ = v_v_1711_;
v_isShared_1733_ = v_isSharedCheck_1738_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_b_1730_);
lean_dec(v_v_1711_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1738_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1734_; lean_object* v___x_1736_; 
lean_inc_ref(v_f_1706_);
v___x_1734_ = l_Lean_IR_MapVars_mapFnBody(v_f_1706_, v_b_1730_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v___x_1734_);
v___x_1736_ = v___x_1732_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1734_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
v___y_1715_ = v___x_1736_;
goto v___jp_1714_;
}
}
}
v___jp_1714_:
{
size_t v___x_1716_; size_t v___x_1717_; lean_object* v___x_1718_; 
v___x_1716_ = ((size_t)1ULL);
v___x_1717_ = lean_usize_add(v_i_1708_, v___x_1716_);
v___x_1718_ = lean_array_uset(v_bs_x27_1713_, v_i_1708_, v___y_1715_);
v_i_1708_ = v___x_1717_;
v_bs_1709_ = v___x_1718_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0___boxed(lean_object* v_f_1739_, lean_object* v_sz_1740_, lean_object* v_i_1741_, lean_object* v_bs_1742_){
_start:
{
size_t v_sz_boxed_1743_; size_t v_i_boxed_1744_; lean_object* v_res_1745_; 
v_sz_boxed_1743_ = lean_unbox_usize(v_sz_1740_);
lean_dec(v_sz_1740_);
v_i_boxed_1744_ = lean_unbox_usize(v_i_1741_);
lean_dec(v_i_1741_);
v_res_1745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(v_f_1739_, v_sz_boxed_1743_, v_i_boxed_1744_, v_bs_1742_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_mapVars(lean_object* v_f_1746_, lean_object* v_b_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_IR_MapVars_mapFnBody(v_f_1746_, v_b_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lam__0(lean_object* v_x_1749_, lean_object* v_y_1750_, lean_object* v_z_1751_){
_start:
{
uint8_t v___x_1752_; 
v___x_1752_ = l_Lean_IR_instBEqVarId_beq(v_x_1749_, v_z_1751_);
if (v___x_1752_ == 0)
{
lean_inc(v_z_1751_);
return v_z_1751_;
}
else
{
lean_inc(v_y_1750_);
return v_y_1750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lam__0___boxed(lean_object* v_x_1753_, lean_object* v_y_1754_, lean_object* v_z_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_IR_FnBody_replaceVar___lam__0(v_x_1753_, v_y_1754_, v_z_1755_);
lean_dec(v_z_1755_);
lean_dec(v_y_1754_);
lean_dec(v_x_1753_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar(lean_object* v_x_1757_, lean_object* v_y_1758_, lean_object* v_b_1759_){
_start:
{
lean_object* v___f_1760_; lean_object* v___x_1761_; 
v___f_1760_ = lean_alloc_closure((void*)(l_Lean_IR_FnBody_replaceVar___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1760_, 0, v_x_1757_);
lean_closure_set(v___f_1760_, 1, v_y_1758_);
v___x_1761_ = l_Lean_IR_MapVars_mapFnBody(v___f_1760_, v_b_1759_);
return v___x_1761_;
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
