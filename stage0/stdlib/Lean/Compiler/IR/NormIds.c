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
uint8_t lean_bool_not(uint8_t);
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
lean_object* v___x_339_; lean_object* v_x_340_; lean_object* v___x_341_; lean_object* v_fst_342_; lean_object* v_snd_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_356_; 
v___x_339_ = lean_array_uget_borrowed(v_as_334_, v_i_335_);
v_x_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_x_340_);
v___x_341_ = l_Lean_IR_UniqueIds_checkId(v_x_340_, v___y_337_);
v_fst_342_ = lean_ctor_get(v___x_341_, 0);
v_snd_343_ = lean_ctor_get(v___x_341_, 1);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_356_ == 0)
{
v___x_345_ = v___x_341_;
v_isShared_346_ = v_isSharedCheck_356_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_snd_343_);
lean_inc(v_fst_342_);
lean_dec(v___x_341_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_356_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
uint8_t v___x_347_; uint8_t v___x_348_; 
v___x_347_ = lean_unbox(v_fst_342_);
lean_dec(v_fst_342_);
v___x_348_ = lean_bool_not(v___x_347_);
if (v___x_348_ == 0)
{
size_t v___x_349_; size_t v___x_350_; 
lean_del_object(v___x_345_);
v___x_349_ = ((size_t)1ULL);
v___x_350_ = lean_usize_add(v_i_335_, v___x_349_);
v_i_335_ = v___x_350_;
v___y_337_ = v_snd_343_;
goto _start;
}
else
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = lean_box(v___x_348_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_352_);
v___x_354_ = v___x_345_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_snd_343_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
else
{
uint8_t v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = 0;
v___x_358_ = lean_box(v___x_357_);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v___y_337_);
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
uint8_t v_____do__lift_370_; lean_object* v___y_371_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_375_ = lean_unsigned_to_nat(0u);
v___x_376_ = lean_array_get_size(v_ps_367_);
v___x_377_ = lean_nat_dec_lt(v___x_375_, v___x_376_);
if (v___x_377_ == 0)
{
v_____do__lift_370_ = v___x_377_;
v___y_371_ = v_a_368_;
goto v___jp_369_;
}
else
{
if (v___x_377_ == 0)
{
v_____do__lift_370_ = v___x_377_;
v___y_371_ = v_a_368_;
goto v___jp_369_;
}
else
{
size_t v___x_378_; size_t v___x_379_; lean_object* v___x_380_; lean_object* v_fst_381_; lean_object* v_snd_382_; uint8_t v___x_383_; 
v___x_378_ = ((size_t)0ULL);
v___x_379_ = lean_usize_of_nat(v___x_376_);
v___x_380_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkParams_spec__0(v_ps_367_, v___x_378_, v___x_379_, v_a_368_);
v_fst_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_fst_381_);
v_snd_382_ = lean_ctor_get(v___x_380_, 1);
lean_inc(v_snd_382_);
lean_dec_ref(v___x_380_);
v___x_383_ = lean_unbox(v_fst_381_);
lean_dec(v_fst_381_);
v_____do__lift_370_ = v___x_383_;
v___y_371_ = v_snd_382_;
goto v___jp_369_;
}
}
v___jp_369_:
{
uint8_t v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = lean_bool_not(v_____do__lift_370_);
v___x_373_ = lean_box(v___x_372_);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v___y_371_);
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkParams___boxed(lean_object* v_ps_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_IR_UniqueIds_checkParams(v_ps_384_, v_a_385_);
lean_dec_ref(v_ps_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkFnBody(lean_object* v_x_387_, lean_object* v_a_388_){
_start:
{
uint8_t v_____do__lift_390_; lean_object* v___y_391_; 
switch(lean_obj_tag(v_x_387_))
{
case 0:
{
lean_object* v_x_395_; lean_object* v_b_396_; lean_object* v___x_397_; lean_object* v_fst_398_; uint8_t v___x_399_; 
v_x_395_ = lean_ctor_get(v_x_387_, 0);
lean_inc(v_x_395_);
v_b_396_ = lean_ctor_get(v_x_387_, 3);
lean_inc(v_b_396_);
lean_dec_ref_known(v_x_387_, 4);
v___x_397_ = l_Lean_IR_UniqueIds_checkId(v_x_395_, v_a_388_);
v_fst_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_fst_398_);
v___x_399_ = lean_unbox(v_fst_398_);
lean_dec(v_fst_398_);
if (v___x_399_ == 0)
{
lean_dec(v_b_396_);
return v___x_397_;
}
else
{
lean_object* v_snd_400_; 
v_snd_400_ = lean_ctor_get(v___x_397_, 1);
lean_inc(v_snd_400_);
lean_dec_ref(v___x_397_);
v_x_387_ = v_b_396_;
v_a_388_ = v_snd_400_;
goto _start;
}
}
case 1:
{
lean_object* v_j_402_; lean_object* v_xs_403_; lean_object* v_b_404_; lean_object* v___x_405_; lean_object* v_fst_406_; uint8_t v___x_407_; 
v_j_402_ = lean_ctor_get(v_x_387_, 0);
lean_inc(v_j_402_);
v_xs_403_ = lean_ctor_get(v_x_387_, 1);
lean_inc_ref(v_xs_403_);
v_b_404_ = lean_ctor_get(v_x_387_, 3);
lean_inc(v_b_404_);
lean_dec_ref_known(v_x_387_, 4);
v___x_405_ = l_Lean_IR_UniqueIds_checkId(v_j_402_, v_a_388_);
v_fst_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_fst_406_);
v___x_407_ = lean_unbox(v_fst_406_);
lean_dec(v_fst_406_);
if (v___x_407_ == 0)
{
lean_dec(v_b_404_);
lean_dec_ref(v_xs_403_);
return v___x_405_;
}
else
{
lean_object* v_snd_408_; lean_object* v___x_409_; lean_object* v_fst_410_; uint8_t v___x_411_; 
v_snd_408_ = lean_ctor_get(v___x_405_, 1);
lean_inc(v_snd_408_);
lean_dec_ref(v___x_405_);
v___x_409_ = l_Lean_IR_UniqueIds_checkParams(v_xs_403_, v_snd_408_);
lean_dec_ref(v_xs_403_);
v_fst_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_fst_410_);
v___x_411_ = lean_unbox(v_fst_410_);
lean_dec(v_fst_410_);
if (v___x_411_ == 0)
{
lean_dec(v_b_404_);
return v___x_409_;
}
else
{
lean_object* v_snd_412_; 
v_snd_412_ = lean_ctor_get(v___x_409_, 1);
lean_inc(v_snd_412_);
lean_dec_ref(v___x_409_);
v_x_387_ = v_b_404_;
v_a_388_ = v_snd_412_;
goto _start;
}
}
}
case 9:
{
lean_object* v_cs_414_; lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v_cs_414_ = lean_ctor_get(v_x_387_, 3);
lean_inc_ref(v_cs_414_);
lean_dec_ref_known(v_x_387_, 4);
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = lean_array_get_size(v_cs_414_);
v___x_417_ = lean_nat_dec_lt(v___x_415_, v___x_416_);
if (v___x_417_ == 0)
{
lean_dec_ref(v_cs_414_);
v_____do__lift_390_ = v___x_417_;
v___y_391_ = v_a_388_;
goto v___jp_389_;
}
else
{
if (v___x_417_ == 0)
{
lean_dec_ref(v_cs_414_);
v_____do__lift_390_ = v___x_417_;
v___y_391_ = v_a_388_;
goto v___jp_389_;
}
else
{
size_t v___x_418_; size_t v___x_419_; lean_object* v___x_420_; lean_object* v_fst_421_; lean_object* v_snd_422_; uint8_t v___x_423_; 
v___x_418_ = ((size_t)0ULL);
v___x_419_ = lean_usize_of_nat(v___x_416_);
v___x_420_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(v_cs_414_, v___x_418_, v___x_419_, v_a_388_);
lean_dec_ref(v_cs_414_);
v_fst_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_fst_421_);
v_snd_422_ = lean_ctor_get(v___x_420_, 1);
lean_inc(v_snd_422_);
lean_dec_ref(v___x_420_);
v___x_423_ = lean_unbox(v_fst_421_);
lean_dec(v_fst_421_);
v_____do__lift_390_ = v___x_423_;
v___y_391_ = v_snd_422_;
goto v___jp_389_;
}
}
}
default: 
{
uint8_t v___x_424_; 
v___x_424_ = l_Lean_IR_FnBody_isTerminal(v_x_387_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_IR_FnBody_body(v_x_387_);
lean_dec(v_x_387_);
v_x_387_ = v___x_425_;
goto _start;
}
else
{
lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec(v_x_387_);
v___x_427_ = lean_box(v___x_424_);
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v_a_388_);
return v___x_428_;
}
}
}
v___jp_389_:
{
uint8_t v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = lean_bool_not(v_____do__lift_390_);
v___x_393_ = lean_box(v___x_392_);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___y_391_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(lean_object* v_as_429_, size_t v_i_430_, size_t v_stop_431_, lean_object* v___y_432_){
_start:
{
uint8_t v___x_433_; 
v___x_433_ = lean_usize_dec_eq(v_i_430_, v_stop_431_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v_fst_437_; lean_object* v_snd_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_451_; 
v___x_434_ = lean_array_uget_borrowed(v_as_429_, v_i_430_);
v___x_435_ = l_Lean_IR_Alt_body(v___x_434_);
v___x_436_ = l_Lean_IR_UniqueIds_checkFnBody(v___x_435_, v___y_432_);
v_fst_437_ = lean_ctor_get(v___x_436_, 0);
v_snd_438_ = lean_ctor_get(v___x_436_, 1);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_451_ == 0)
{
v___x_440_ = v___x_436_;
v_isShared_441_ = v_isSharedCheck_451_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_snd_438_);
lean_inc(v_fst_437_);
lean_dec(v___x_436_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_451_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
uint8_t v___x_442_; uint8_t v___x_443_; 
v___x_442_ = lean_unbox(v_fst_437_);
lean_dec(v_fst_437_);
v___x_443_ = lean_bool_not(v___x_442_);
if (v___x_443_ == 0)
{
size_t v___x_444_; size_t v___x_445_; 
lean_del_object(v___x_440_);
v___x_444_ = ((size_t)1ULL);
v___x_445_ = lean_usize_add(v_i_430_, v___x_444_);
v_i_430_ = v___x_445_;
v___y_432_ = v_snd_438_;
goto _start;
}
else
{
lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_447_ = lean_box(v___x_443_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_447_);
v___x_449_ = v___x_440_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_snd_438_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
else
{
uint8_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = 0;
v___x_453_ = lean_box(v___x_452_);
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v___y_432_);
return v___x_454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0___boxed(lean_object* v_as_455_, lean_object* v_i_456_, lean_object* v_stop_457_, lean_object* v___y_458_){
_start:
{
size_t v_i_boxed_459_; size_t v_stop_boxed_460_; lean_object* v_res_461_; 
v_i_boxed_459_ = lean_unbox_usize(v_i_456_);
lean_dec(v_i_456_);
v_stop_boxed_460_ = lean_unbox_usize(v_stop_457_);
lean_dec(v_stop_457_);
v_res_461_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(v_as_455_, v_i_boxed_459_, v_stop_boxed_460_, v___y_458_);
lean_dec_ref(v_as_455_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkDecl(lean_object* v_x_462_, lean_object* v_a_463_){
_start:
{
if (lean_obj_tag(v_x_462_) == 0)
{
lean_object* v_xs_464_; lean_object* v_body_465_; lean_object* v___x_466_; lean_object* v_fst_467_; uint8_t v___x_468_; 
v_xs_464_ = lean_ctor_get(v_x_462_, 1);
lean_inc_ref(v_xs_464_);
v_body_465_ = lean_ctor_get(v_x_462_, 3);
lean_inc(v_body_465_);
lean_dec_ref_known(v_x_462_, 5);
v___x_466_ = l_Lean_IR_UniqueIds_checkParams(v_xs_464_, v_a_463_);
lean_dec_ref(v_xs_464_);
v_fst_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_fst_467_);
v___x_468_ = lean_unbox(v_fst_467_);
lean_dec(v_fst_467_);
if (v___x_468_ == 0)
{
lean_dec(v_body_465_);
return v___x_466_;
}
else
{
lean_object* v_snd_469_; lean_object* v___x_470_; 
v_snd_469_ = lean_ctor_get(v___x_466_, 1);
lean_inc(v_snd_469_);
lean_dec_ref(v___x_466_);
v___x_470_ = l_Lean_IR_UniqueIds_checkFnBody(v_body_465_, v_snd_469_);
return v___x_470_;
}
}
else
{
lean_object* v_xs_471_; lean_object* v___x_472_; 
v_xs_471_ = lean_ctor_get(v_x_462_, 1);
lean_inc_ref(v_xs_471_);
lean_dec_ref_known(v_x_462_, 4);
v___x_472_ = l_Lean_IR_UniqueIds_checkParams(v_xs_471_, v_a_463_);
lean_dec_ref(v_xs_471_);
return v___x_472_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Decl_uniqueIds(lean_object* v_d_473_){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_fst_476_; uint8_t v___x_477_; 
v___x_474_ = lean_box(1);
v___x_475_ = l_Lean_IR_UniqueIds_checkDecl(v_d_473_, v___x_474_);
v_fst_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_fst_476_);
lean_dec_ref(v___x_475_);
v___x_477_ = lean_unbox(v_fst_476_);
lean_dec(v_fst_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_uniqueIds___boxed(lean_object* v_d_478_){
_start:
{
uint8_t v_res_479_; lean_object* v_r_480_; 
v_res_479_ = l_Lean_IR_Decl_uniqueIds(v_d_478_);
v_r_480_ = lean_box(v_res_479_);
return v_r_480_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(lean_object* v_t_481_, lean_object* v_k_482_){
_start:
{
if (lean_obj_tag(v_t_481_) == 0)
{
lean_object* v_k_483_; lean_object* v_v_484_; lean_object* v_l_485_; lean_object* v_r_486_; uint8_t v___x_487_; 
v_k_483_ = lean_ctor_get(v_t_481_, 1);
v_v_484_ = lean_ctor_get(v_t_481_, 2);
v_l_485_ = lean_ctor_get(v_t_481_, 3);
v_r_486_ = lean_ctor_get(v_t_481_, 4);
v___x_487_ = lean_nat_dec_lt(v_k_482_, v_k_483_);
if (v___x_487_ == 0)
{
uint8_t v___x_488_; 
v___x_488_ = lean_nat_dec_eq(v_k_482_, v_k_483_);
if (v___x_488_ == 0)
{
v_t_481_ = v_r_486_;
goto _start;
}
else
{
lean_object* v___x_490_; 
lean_inc(v_v_484_);
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v_v_484_);
return v___x_490_;
}
}
else
{
v_t_481_ = v_l_485_;
goto _start;
}
}
else
{
lean_object* v___x_492_; 
v___x_492_ = lean_box(0);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg___boxed(lean_object* v_t_493_, lean_object* v_k_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_t_493_, v_k_494_);
lean_dec(v_k_494_);
lean_dec(v_t_493_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normIndex(lean_object* v_x_496_, lean_object* v_m_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_m_497_, v_x_496_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_inc(v_x_496_);
return v_x_496_;
}
else
{
lean_object* v_val_499_; 
v_val_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_val_499_);
lean_dec_ref_known(v___x_498_, 1);
return v_val_499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normIndex___boxed(lean_object* v_x_500_, lean_object* v_m_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_IR_NormalizeIds_normIndex(v_x_500_, v_m_501_);
lean_dec(v_m_501_);
lean_dec(v_x_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0(lean_object* v_00_u03b4_503_, lean_object* v_t_504_, lean_object* v_k_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_t_504_, v_k_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___boxed(lean_object* v_00_u03b4_507_, lean_object* v_t_508_, lean_object* v_k_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0(v_00_u03b4_507_, v_t_508_, v_k_509_);
lean_dec(v_k_509_);
lean_dec(v_t_508_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normVar(lean_object* v_x_511_, lean_object* v_a_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_IR_NormalizeIds_normIndex(v_x_511_, v_a_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normVar___boxed(lean_object* v_x_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_IR_NormalizeIds_normVar(v_x_514_, v_a_515_);
lean_dec(v_a_515_);
lean_dec(v_x_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normJP(lean_object* v_x_517_, lean_object* v_a_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_IR_NormalizeIds_normIndex(v_x_517_, v_a_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normJP___boxed(lean_object* v_x_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_IR_NormalizeIds_normJP(v_x_520_, v_a_521_);
lean_dec(v_a_521_);
lean_dec(v_x_520_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArg(lean_object* v_x_523_, lean_object* v_a_524_){
_start:
{
if (lean_obj_tag(v_x_523_) == 0)
{
lean_object* v_id_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_533_; 
v_id_525_ = lean_ctor_get(v_x_523_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v_x_523_);
if (v_isSharedCheck_533_ == 0)
{
v___x_527_ = v_x_523_;
v_isShared_528_ = v_isSharedCheck_533_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_id_525_);
lean_dec(v_x_523_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_533_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_529_ = l_Lean_IR_NormalizeIds_normIndex(v_id_525_, v_a_524_);
lean_dec(v_id_525_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_529_);
v___x_531_ = v___x_527_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
else
{
return v_x_523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArg___boxed(lean_object* v_x_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_IR_NormalizeIds_normArg(v_x_534_, v_a_535_);
lean_dec(v_a_535_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(lean_object* v_m_537_, size_t v_sz_538_, size_t v_i_539_, lean_object* v_bs_540_){
_start:
{
uint8_t v___x_541_; 
v___x_541_ = lean_usize_dec_lt(v_i_539_, v_sz_538_);
if (v___x_541_ == 0)
{
return v_bs_540_;
}
else
{
lean_object* v_v_542_; lean_object* v___x_543_; lean_object* v_bs_x27_544_; lean_object* v___x_545_; size_t v___x_546_; size_t v___x_547_; lean_object* v___x_548_; 
v_v_542_ = lean_array_uget(v_bs_540_, v_i_539_);
v___x_543_ = lean_unsigned_to_nat(0u);
v_bs_x27_544_ = lean_array_uset(v_bs_540_, v_i_539_, v___x_543_);
v___x_545_ = l_Lean_IR_NormalizeIds_normArg(v_v_542_, v_m_537_);
v___x_546_ = ((size_t)1ULL);
v___x_547_ = lean_usize_add(v_i_539_, v___x_546_);
v___x_548_ = lean_array_uset(v_bs_x27_544_, v_i_539_, v___x_545_);
v_i_539_ = v___x_547_;
v_bs_540_ = v___x_548_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0___boxed(lean_object* v_m_550_, lean_object* v_sz_551_, lean_object* v_i_552_, lean_object* v_bs_553_){
_start:
{
size_t v_sz_boxed_554_; size_t v_i_boxed_555_; lean_object* v_res_556_; 
v_sz_boxed_554_ = lean_unbox_usize(v_sz_551_);
lean_dec(v_sz_551_);
v_i_boxed_555_ = lean_unbox_usize(v_i_552_);
lean_dec(v_i_552_);
v_res_556_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(v_m_550_, v_sz_boxed_554_, v_i_boxed_555_, v_bs_553_);
lean_dec(v_m_550_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArgs(lean_object* v_as_557_, lean_object* v_m_558_){
_start:
{
size_t v_sz_559_; size_t v___x_560_; lean_object* v___x_561_; 
v_sz_559_ = lean_array_size(v_as_557_);
v___x_560_ = ((size_t)0ULL);
v___x_561_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(v_m_558_, v_sz_559_, v___x_560_, v_as_557_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArgs___boxed(lean_object* v_as_562_, lean_object* v_m_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_IR_NormalizeIds_normArgs(v_as_562_, v_m_563_);
lean_dec(v_m_563_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normExpr(lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
switch(lean_obj_tag(v_x_565_))
{
case 0:
{
lean_object* v_i_567_; lean_object* v_ys_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_576_; 
v_i_567_ = lean_ctor_get(v_x_565_, 0);
v_ys_568_ = lean_ctor_get(v_x_565_, 1);
v_isSharedCheck_576_ = !lean_is_exclusive(v_x_565_);
if (v_isSharedCheck_576_ == 0)
{
v___x_570_ = v_x_565_;
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_ys_568_);
lean_inc(v_i_567_);
lean_dec(v_x_565_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_572_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_568_, v_x_566_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 1, v___x_572_);
v___x_574_ = v___x_570_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_i_567_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
case 1:
{
lean_object* v_n_577_; lean_object* v_x_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_586_; 
v_n_577_ = lean_ctor_get(v_x_565_, 0);
v_x_578_ = lean_ctor_get(v_x_565_, 1);
v_isSharedCheck_586_ = !lean_is_exclusive(v_x_565_);
if (v_isSharedCheck_586_ == 0)
{
v___x_580_ = v_x_565_;
v_isShared_581_ = v_isSharedCheck_586_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_x_578_);
lean_inc(v_n_577_);
lean_dec(v_x_565_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_586_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_582_ = l_Lean_IR_NormalizeIds_normIndex(v_x_578_, v_x_566_);
lean_dec(v_x_578_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___x_582_);
v___x_584_ = v___x_580_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_n_577_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
case 2:
{
lean_object* v_x_587_; lean_object* v_i_588_; uint8_t v_updtHeader_589_; lean_object* v_ys_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_599_; 
v_x_587_ = lean_ctor_get(v_x_565_, 0);
v_i_588_ = lean_ctor_get(v_x_565_, 1);
v_updtHeader_589_ = lean_ctor_get_uint8(v_x_565_, sizeof(void*)*3);
v_ys_590_ = lean_ctor_get(v_x_565_, 2);
v_isSharedCheck_599_ = !lean_is_exclusive(v_x_565_);
if (v_isSharedCheck_599_ == 0)
{
v___x_592_ = v_x_565_;
v_isShared_593_ = v_isSharedCheck_599_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_ys_590_);
lean_inc(v_i_588_);
lean_inc(v_x_587_);
lean_dec(v_x_565_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_599_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_594_ = l_Lean_IR_NormalizeIds_normIndex(v_x_587_, v_x_566_);
lean_dec(v_x_587_);
v___x_595_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_590_, v_x_566_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 2, v___x_595_);
lean_ctor_set(v___x_592_, 0, v___x_594_);
v___x_597_ = v___x_592_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_i_588_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v___x_595_);
lean_ctor_set_uint8(v_reuseFailAlloc_598_, sizeof(void*)*3, v_updtHeader_589_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
case 3:
{
lean_object* v_i_600_; lean_object* v_x_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_609_; 
v_i_600_ = lean_ctor_get(v_x_565_, 0);
v_x_601_ = lean_ctor_get(v_x_565_, 1);
v_isSharedCheck_609_ = !lean_is_exclusive(v_x_565_);
if (v_isSharedCheck_609_ == 0)
{
v___x_603_ = v_x_565_;
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_x_601_);
lean_inc(v_i_600_);
lean_dec(v_x_565_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_605_ = l_Lean_IR_NormalizeIds_normIndex(v_x_601_, v_x_566_);
lean_dec(v_x_601_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 1, v___x_605_);
v___x_607_ = v___x_603_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_i_600_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
case 4:
{
lean_object* v_i_610_; lean_object* v_x_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_619_; 
v_i_610_ = lean_ctor_get(v_x_565_, 0);
v_x_611_ = lean_ctor_get(v_x_565_, 1);
v_isSharedCheck_619_ = !lean_is_exclusive(v_x_565_);
if (v_isSharedCheck_619_ == 0)
{
v___x_613_ = v_x_565_;
v_isShared_614_ = v_isSharedCheck_619_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_x_611_);
lean_inc(v_i_610_);
lean_dec(v_x_565_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_619_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = l_Lean_IR_NormalizeIds_normIndex(v_x_611_, v_x_566_);
lean_dec(v_x_611_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v___x_615_);
v___x_617_ = v___x_613_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_i_610_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v___x_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
case 5:
{
lean_object* v_n_620_; lean_object* v_offset_621_; lean_object* v_x_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_630_; 
v_n_620_ = lean_ctor_get(v_x_565_, 0);
v_offset_621_ = lean_ctor_get(v_x_565_, 1);
v_x_622_ = lean_ctor_get(v_x_565_, 2);
v_isSharedCheck_630_ = !lean_is_exclusive(v_x_565_);
if (v_isSharedCheck_630_ == 0)
{
v___x_624_ = v_x_565_;
v_isShared_625_ = v_isSharedCheck_630_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_x_622_);
lean_inc(v_offset_621_);
lean_inc(v_n_620_);
lean_dec(v_x_565_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_630_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_626_ = l_Lean_IR_NormalizeIds_normIndex(v_x_622_, v_x_566_);
lean_dec(v_x_622_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 2, v___x_626_);
v___x_628_ = v___x_624_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_n_620_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_offset_621_);
lean_ctor_set(v_reuseFailAlloc_629_, 2, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
case 6:
{
lean_object* v_c_631_; lean_object* v_ys_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_640_; 
v_c_631_ = lean_ctor_get(v_x_565_, 0);
v_ys_632_ = lean_ctor_get(v_x_565_, 1);
v_isSharedCheck_640_ = !lean_is_exclusive(v_x_565_);
if (v_isSharedCheck_640_ == 0)
{
v___x_634_ = v_x_565_;
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_ys_632_);
lean_inc(v_c_631_);
lean_dec(v_x_565_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_636_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_632_, v_x_566_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v___x_636_);
v___x_638_ = v___x_634_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_c_631_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
case 7:
{
lean_object* v_c_641_; lean_object* v_ys_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_650_; 
v_c_641_ = lean_ctor_get(v_x_565_, 0);
v_ys_642_ = lean_ctor_get(v_x_565_, 1);
v_isSharedCheck_650_ = !lean_is_exclusive(v_x_565_);
if (v_isSharedCheck_650_ == 0)
{
v___x_644_ = v_x_565_;
v_isShared_645_ = v_isSharedCheck_650_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_ys_642_);
lean_inc(v_c_641_);
lean_dec(v_x_565_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_650_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_646_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_642_, v_x_566_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 1, v___x_646_);
v___x_648_ = v___x_644_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_c_641_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
case 8:
{
lean_object* v_x_651_; lean_object* v_ys_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_661_; 
v_x_651_ = lean_ctor_get(v_x_565_, 0);
v_ys_652_ = lean_ctor_get(v_x_565_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v_x_565_);
if (v_isSharedCheck_661_ == 0)
{
v___x_654_ = v_x_565_;
v_isShared_655_ = v_isSharedCheck_661_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_ys_652_);
lean_inc(v_x_651_);
lean_dec(v_x_565_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_661_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_656_ = l_Lean_IR_NormalizeIds_normIndex(v_x_651_, v_x_566_);
lean_dec(v_x_651_);
v___x_657_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_652_, v_x_566_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 1, v___x_657_);
lean_ctor_set(v___x_654_, 0, v___x_656_);
v___x_659_ = v___x_654_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
case 9:
{
lean_object* v_ty_662_; lean_object* v_x_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_671_; 
v_ty_662_ = lean_ctor_get(v_x_565_, 0);
v_x_663_ = lean_ctor_get(v_x_565_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v_x_565_);
if (v_isSharedCheck_671_ == 0)
{
v___x_665_ = v_x_565_;
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_x_663_);
lean_inc(v_ty_662_);
lean_dec(v_x_565_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = l_Lean_IR_NormalizeIds_normIndex(v_x_663_, v_x_566_);
lean_dec(v_x_663_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___x_667_);
v___x_669_ = v___x_665_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_ty_662_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
case 10:
{
lean_object* v_x_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_680_; 
v_x_672_ = lean_ctor_get(v_x_565_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v_x_565_);
if (v_isSharedCheck_680_ == 0)
{
v___x_674_ = v_x_565_;
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_x_672_);
lean_dec(v_x_565_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = l_Lean_IR_NormalizeIds_normIndex(v_x_672_, v_x_566_);
lean_dec(v_x_672_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_676_);
v___x_678_ = v___x_674_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
case 11:
{
return v_x_565_;
}
default: 
{
lean_object* v_x_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_689_; 
v_x_681_ = lean_ctor_get(v_x_565_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v_x_565_);
if (v_isSharedCheck_689_ == 0)
{
v___x_683_ = v_x_565_;
v_isShared_684_ = v_isSharedCheck_689_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_x_681_);
lean_dec(v_x_565_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_689_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_685_ = l_Lean_IR_NormalizeIds_normIndex(v_x_681_, v_x_566_);
lean_dec(v_x_681_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_685_);
v___x_687_ = v___x_683_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normExpr___boxed(lean_object* v_x_690_, lean_object* v_x_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_IR_NormalizeIds_normExpr(v_x_690_, v_x_691_);
lean_dec(v_x_691_);
return v_res_692_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_NormalizeIds_withVar___redArg___lam__0(lean_object* v_x_693_, lean_object* v_y_694_){
_start:
{
uint8_t v___x_695_; 
v___x_695_ = lean_nat_dec_lt(v_x_693_, v_y_694_);
if (v___x_695_ == 0)
{
uint8_t v___x_696_; 
v___x_696_ = lean_nat_dec_eq(v_x_693_, v_y_694_);
if (v___x_696_ == 0)
{
uint8_t v___x_697_; 
v___x_697_ = 2;
return v___x_697_;
}
else
{
uint8_t v___x_698_; 
v___x_698_ = 1;
return v___x_698_;
}
}
else
{
uint8_t v___x_699_; 
v___x_699_ = 0;
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg___lam__0___boxed(lean_object* v_x_700_, lean_object* v_y_701_){
_start:
{
uint8_t v_res_702_; lean_object* v_r_703_; 
v_res_702_ = l_Lean_IR_NormalizeIds_withVar___redArg___lam__0(v_x_700_, v_y_701_);
lean_dec(v_y_701_);
lean_dec(v_x_700_);
v_r_703_ = lean_box(v_res_702_);
return v_r_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg(lean_object* v_x_705_, lean_object* v_k_706_, lean_object* v_m_707_, lean_object* v_a_708_){
_start:
{
lean_object* v___f_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___f_709_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_710_ = lean_unsigned_to_nat(1u);
v___x_711_ = lean_nat_add(v_a_708_, v___x_710_);
lean_inc(v_m_707_);
lean_inc(v_a_708_);
v___x_712_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_709_, v_x_705_, v_a_708_, v_m_707_);
v___x_713_ = lean_apply_3(v_k_706_, v_a_708_, v___x_712_, v___x_711_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg___boxed(lean_object* v_x_714_, lean_object* v_k_715_, lean_object* v_m_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_IR_NormalizeIds_withVar___redArg(v_x_714_, v_k_715_, v_m_716_, v_a_717_);
lean_dec(v_m_716_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar(lean_object* v_00_u03b1_719_, lean_object* v_x_720_, lean_object* v_k_721_, lean_object* v_m_722_, lean_object* v_a_723_){
_start:
{
lean_object* v___f_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___f_724_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = lean_nat_add(v_a_723_, v___x_725_);
lean_inc(v_m_722_);
lean_inc(v_a_723_);
v___x_727_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_724_, v_x_720_, v_a_723_, v_m_722_);
v___x_728_ = lean_apply_3(v_k_721_, v_a_723_, v___x_727_, v___x_726_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___boxed(lean_object* v_00_u03b1_729_, lean_object* v_x_730_, lean_object* v_k_731_, lean_object* v_m_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_IR_NormalizeIds_withVar(v_00_u03b1_729_, v_x_730_, v_k_731_, v_m_732_, v_a_733_);
lean_dec(v_m_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___redArg(lean_object* v_x_735_, lean_object* v_k_736_, lean_object* v_m_737_, lean_object* v_a_738_){
_start:
{
lean_object* v___f_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___f_739_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = lean_nat_add(v_a_738_, v___x_740_);
lean_inc(v_m_737_);
lean_inc(v_a_738_);
v___x_742_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_739_, v_x_735_, v_a_738_, v_m_737_);
v___x_743_ = lean_apply_3(v_k_736_, v_a_738_, v___x_742_, v___x_741_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___redArg___boxed(lean_object* v_x_744_, lean_object* v_k_745_, lean_object* v_m_746_, lean_object* v_a_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_IR_NormalizeIds_withJP___redArg(v_x_744_, v_k_745_, v_m_746_, v_a_747_);
lean_dec(v_m_746_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP(lean_object* v_00_u03b1_749_, lean_object* v_x_750_, lean_object* v_k_751_, lean_object* v_m_752_, lean_object* v_a_753_){
_start:
{
lean_object* v___f_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___f_754_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_755_ = lean_unsigned_to_nat(1u);
v___x_756_ = lean_nat_add(v_a_753_, v___x_755_);
lean_inc(v_m_752_);
lean_inc(v_a_753_);
v___x_757_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_754_, v_x_750_, v_a_753_, v_m_752_);
v___x_758_ = lean_apply_3(v_k_751_, v_a_753_, v___x_757_, v___x_756_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___boxed(lean_object* v_00_u03b1_759_, lean_object* v_x_760_, lean_object* v_k_761_, lean_object* v_m_762_, lean_object* v_a_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_IR_NormalizeIds_withJP(v_00_u03b1_759_, v_x_760_, v_k_761_, v_m_762_, v_a_763_);
lean_dec(v_m_762_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__0(lean_object* v_fst_765_, lean_object* v_x_766_){
_start:
{
lean_object* v_x_767_; uint8_t v_borrow_768_; lean_object* v_ty_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_777_; 
v_x_767_ = lean_ctor_get(v_x_766_, 0);
v_borrow_768_ = lean_ctor_get_uint8(v_x_766_, sizeof(void*)*2);
v_ty_769_ = lean_ctor_get(v_x_766_, 1);
v_isSharedCheck_777_ = !lean_is_exclusive(v_x_766_);
if (v_isSharedCheck_777_ == 0)
{
v___x_771_ = v_x_766_;
v_isShared_772_ = v_isSharedCheck_777_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_ty_769_);
lean_inc(v_x_767_);
lean_dec(v_x_766_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_777_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_773_ = l_Lean_IR_NormalizeIds_normIndex(v_x_767_, v_fst_765_);
lean_dec(v_x_767_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_773_);
v___x_775_ = v___x_771_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_ty_769_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, sizeof(void*)*2, v_borrow_768_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed(lean_object* v_fst_778_, lean_object* v_x_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_IR_NormalizeIds_withParams___redArg___lam__0(v_fst_778_, v_x_779_);
lean_dec(v_fst_778_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__2(lean_object* v___f_781_, lean_object* v_m_782_, lean_object* v_p_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v_x_785_ = lean_ctor_get(v_p_783_, 0);
lean_inc(v_x_785_);
lean_dec_ref(v_p_783_);
v___x_786_ = lean_unsigned_to_nat(1u);
v___x_787_ = lean_nat_add(v___y_784_, v___x_786_);
v___x_788_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_781_, v_x_785_, v___y_784_, v_m_782_);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
lean_ctor_set(v___x_789_, 1, v___x_787_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg(lean_object* v_ps_837_, lean_object* v_k_838_, lean_object* v_m_839_, lean_object* v_a_840_){
_start:
{
lean_object* v___x_841_; lean_object* v_fst_843_; lean_object* v_snd_844_; lean_object* v___y_851_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_841_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__9));
v___x_854_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__19));
v___x_855_ = lean_unsigned_to_nat(0u);
v___x_856_ = lean_array_get_size(v_ps_837_);
v___x_857_ = lean_nat_dec_lt(v___x_855_, v___x_856_);
if (v___x_857_ == 0)
{
lean_inc(v_m_839_);
v_fst_843_ = v_m_839_;
v_snd_844_ = v_a_840_;
goto v___jp_842_;
}
else
{
lean_object* v___f_858_; uint8_t v___x_859_; 
v___f_858_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__20));
v___x_859_ = lean_nat_dec_le(v___x_856_, v___x_856_);
if (v___x_859_ == 0)
{
if (v___x_857_ == 0)
{
lean_inc(v_m_839_);
v_fst_843_ = v_m_839_;
v_snd_844_ = v_a_840_;
goto v___jp_842_;
}
else
{
size_t v___x_860_; size_t v___x_861_; lean_object* v___x_793__overap_862_; lean_object* v___x_863_; 
v___x_860_ = ((size_t)0ULL);
v___x_861_ = lean_usize_of_nat(v___x_856_);
lean_inc(v_m_839_);
lean_inc_ref(v_ps_837_);
v___x_793__overap_862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_854_, v___f_858_, v_ps_837_, v___x_860_, v___x_861_, v_m_839_);
v___x_863_ = lean_apply_1(v___x_793__overap_862_, v_a_840_);
v___y_851_ = v___x_863_;
goto v___jp_850_;
}
}
else
{
size_t v___x_864_; size_t v___x_865_; lean_object* v___x_798__overap_866_; lean_object* v___x_867_; 
v___x_864_ = ((size_t)0ULL);
v___x_865_ = lean_usize_of_nat(v___x_856_);
lean_inc(v_m_839_);
lean_inc_ref(v_ps_837_);
v___x_798__overap_866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_854_, v___f_858_, v_ps_837_, v___x_864_, v___x_865_, v_m_839_);
v___x_867_ = lean_apply_1(v___x_798__overap_866_, v_a_840_);
v___y_851_ = v___x_867_;
goto v___jp_850_;
}
}
v___jp_842_:
{
lean_object* v___f_845_; size_t v_sz_846_; size_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
lean_inc(v_fst_843_);
v___f_845_ = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_845_, 0, v_fst_843_);
v_sz_846_ = lean_array_size(v_ps_837_);
v___x_847_ = ((size_t)0ULL);
v___x_848_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_841_, v___f_845_, v_sz_846_, v___x_847_, v_ps_837_);
v___x_849_ = lean_apply_3(v_k_838_, v___x_848_, v_fst_843_, v_snd_844_);
return v___x_849_;
}
v___jp_850_:
{
lean_object* v_fst_852_; lean_object* v_snd_853_; 
v_fst_852_ = lean_ctor_get(v___y_851_, 0);
lean_inc(v_fst_852_);
v_snd_853_ = lean_ctor_get(v___y_851_, 1);
lean_inc(v_snd_853_);
lean_dec_ref(v___y_851_);
v_fst_843_ = v_fst_852_;
v_snd_844_ = v_snd_853_;
goto v___jp_842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___boxed(lean_object* v_ps_868_, lean_object* v_k_869_, lean_object* v_m_870_, lean_object* v_a_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_IR_NormalizeIds_withParams___redArg(v_ps_868_, v_k_869_, v_m_870_, v_a_871_);
lean_dec(v_m_870_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams(lean_object* v_00_u03b1_873_, lean_object* v_ps_874_, lean_object* v_k_875_, lean_object* v_m_876_, lean_object* v_a_877_){
_start:
{
lean_object* v___x_878_; lean_object* v_fst_880_; lean_object* v_snd_881_; lean_object* v___y_888_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_878_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__9));
v___x_891_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__19));
v___x_892_ = lean_unsigned_to_nat(0u);
v___x_893_ = lean_array_get_size(v_ps_874_);
v___x_894_ = lean_nat_dec_lt(v___x_892_, v___x_893_);
if (v___x_894_ == 0)
{
lean_inc(v_m_876_);
v_fst_880_ = v_m_876_;
v_snd_881_ = v_a_877_;
goto v___jp_879_;
}
else
{
lean_object* v___f_895_; uint8_t v___x_896_; 
v___f_895_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__20));
v___x_896_ = lean_nat_dec_le(v___x_893_, v___x_893_);
if (v___x_896_ == 0)
{
if (v___x_894_ == 0)
{
lean_inc(v_m_876_);
v_fst_880_ = v_m_876_;
v_snd_881_ = v_a_877_;
goto v___jp_879_;
}
else
{
size_t v___x_897_; size_t v___x_898_; lean_object* v___x_975__overap_899_; lean_object* v___x_900_; 
v___x_897_ = ((size_t)0ULL);
v___x_898_ = lean_usize_of_nat(v___x_893_);
lean_inc(v_m_876_);
lean_inc_ref(v_ps_874_);
v___x_975__overap_899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_891_, v___f_895_, v_ps_874_, v___x_897_, v___x_898_, v_m_876_);
v___x_900_ = lean_apply_1(v___x_975__overap_899_, v_a_877_);
v___y_888_ = v___x_900_;
goto v___jp_887_;
}
}
else
{
size_t v___x_901_; size_t v___x_902_; lean_object* v___x_978__overap_903_; lean_object* v___x_904_; 
v___x_901_ = ((size_t)0ULL);
v___x_902_ = lean_usize_of_nat(v___x_893_);
lean_inc(v_m_876_);
lean_inc_ref(v_ps_874_);
v___x_978__overap_903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_891_, v___f_895_, v_ps_874_, v___x_901_, v___x_902_, v_m_876_);
v___x_904_ = lean_apply_1(v___x_978__overap_903_, v_a_877_);
v___y_888_ = v___x_904_;
goto v___jp_887_;
}
}
v___jp_879_:
{
lean_object* v___f_882_; size_t v_sz_883_; size_t v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
lean_inc(v_fst_880_);
v___f_882_ = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_882_, 0, v_fst_880_);
v_sz_883_ = lean_array_size(v_ps_874_);
v___x_884_ = ((size_t)0ULL);
v___x_885_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_878_, v___f_882_, v_sz_883_, v___x_884_, v_ps_874_);
v___x_886_ = lean_apply_3(v_k_875_, v___x_885_, v_fst_880_, v_snd_881_);
return v___x_886_;
}
v___jp_887_:
{
lean_object* v_fst_889_; lean_object* v_snd_890_; 
v_fst_889_ = lean_ctor_get(v___y_888_, 0);
lean_inc(v_fst_889_);
v_snd_890_ = lean_ctor_get(v___y_888_, 1);
lean_inc(v_snd_890_);
lean_dec_ref(v___y_888_);
v_fst_880_ = v_fst_889_;
v_snd_881_ = v_snd_890_;
goto v___jp_879_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___boxed(lean_object* v_00_u03b1_905_, lean_object* v_ps_906_, lean_object* v_k_907_, lean_object* v_m_908_, lean_object* v_a_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_IR_NormalizeIds_withParams(v_00_u03b1_905_, v_ps_906_, v_k_907_, v_m_908_, v_a_909_);
lean_dec(v_m_908_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_instMonadLiftMN___lam__0(lean_object* v_00_u03b1_911_, lean_object* v_x_912_, lean_object* v_m_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_apply_1(v_x_912_, v_m_913_);
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v___y_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(lean_object* v_fst_919_, size_t v_sz_920_, size_t v_i_921_, lean_object* v_bs_922_){
_start:
{
uint8_t v___x_923_; 
v___x_923_ = lean_usize_dec_lt(v_i_921_, v_sz_920_);
if (v___x_923_ == 0)
{
return v_bs_922_;
}
else
{
lean_object* v_v_924_; lean_object* v_x_925_; uint8_t v_borrow_926_; lean_object* v_ty_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_941_; 
v_v_924_ = lean_array_uget(v_bs_922_, v_i_921_);
v_x_925_ = lean_ctor_get(v_v_924_, 0);
v_borrow_926_ = lean_ctor_get_uint8(v_v_924_, sizeof(void*)*2);
v_ty_927_ = lean_ctor_get(v_v_924_, 1);
v_isSharedCheck_941_ = !lean_is_exclusive(v_v_924_);
if (v_isSharedCheck_941_ == 0)
{
v___x_929_ = v_v_924_;
v_isShared_930_ = v_isSharedCheck_941_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_ty_927_);
lean_inc(v_x_925_);
lean_dec(v_v_924_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_941_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v_bs_x27_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_931_ = lean_unsigned_to_nat(0u);
v_bs_x27_932_ = lean_array_uset(v_bs_922_, v_i_921_, v___x_931_);
v___x_933_ = l_Lean_IR_NormalizeIds_normIndex(v_x_925_, v_fst_919_);
lean_dec(v_x_925_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_933_);
v___x_935_ = v___x_929_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_933_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_ty_927_);
lean_ctor_set_uint8(v_reuseFailAlloc_940_, sizeof(void*)*2, v_borrow_926_);
v___x_935_ = v_reuseFailAlloc_940_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
size_t v___x_936_; size_t v___x_937_; lean_object* v___x_938_; 
v___x_936_ = ((size_t)1ULL);
v___x_937_ = lean_usize_add(v_i_921_, v___x_936_);
v___x_938_ = lean_array_uset(v_bs_x27_932_, v_i_921_, v___x_935_);
v_i_921_ = v___x_937_;
v_bs_922_ = v___x_938_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0___boxed(lean_object* v_fst_942_, lean_object* v_sz_943_, lean_object* v_i_944_, lean_object* v_bs_945_){
_start:
{
size_t v_sz_boxed_946_; size_t v_i_boxed_947_; lean_object* v_res_948_; 
v_sz_boxed_946_ = lean_unbox_usize(v_sz_943_);
lean_dec(v_sz_943_);
v_i_boxed_947_ = lean_unbox_usize(v_i_944_);
lean_dec(v_i_944_);
v_res_948_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(v_fst_942_, v_sz_boxed_946_, v_i_boxed_947_, v_bs_945_);
lean_dec(v_fst_942_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(lean_object* v_as_949_, size_t v_i_950_, size_t v_stop_951_, lean_object* v_b_952_, lean_object* v___y_953_){
_start:
{
uint8_t v___x_954_; 
v___x_954_ = lean_usize_dec_eq(v_i_950_, v_stop_951_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; lean_object* v_x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; size_t v___x_960_; size_t v___x_961_; 
v___x_955_ = lean_array_uget_borrowed(v_as_949_, v_i_950_);
v_x_956_ = lean_ctor_get(v___x_955_, 0);
v___x_957_ = lean_unsigned_to_nat(1u);
v___x_958_ = lean_nat_add(v___y_953_, v___x_957_);
lean_inc(v_x_956_);
v___x_959_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_x_956_, v___y_953_, v_b_952_);
v___x_960_ = ((size_t)1ULL);
v___x_961_ = lean_usize_add(v_i_950_, v___x_960_);
v_i_950_ = v___x_961_;
v_b_952_ = v___x_959_;
v___y_953_ = v___x_958_;
goto _start;
}
else
{
lean_object* v___x_963_; 
v___x_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_963_, 0, v_b_952_);
lean_ctor_set(v___x_963_, 1, v___y_953_);
return v___x_963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1___boxed(lean_object* v_as_964_, lean_object* v_i_965_, lean_object* v_stop_966_, lean_object* v_b_967_, lean_object* v___y_968_){
_start:
{
size_t v_i_boxed_969_; size_t v_stop_boxed_970_; lean_object* v_res_971_; 
v_i_boxed_969_ = lean_unbox_usize(v_i_965_);
lean_dec(v_i_965_);
v_stop_boxed_970_ = lean_unbox_usize(v_stop_966_);
lean_dec(v_stop_966_);
v_res_971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_as_964_, v_i_boxed_969_, v_stop_boxed_970_, v_b_967_, v___y_968_);
lean_dec_ref(v_as_964_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normFnBody(lean_object* v_x_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
switch(lean_obj_tag(v_x_972_))
{
case 0:
{
lean_object* v_x_975_; lean_object* v_ty_976_; lean_object* v_e_977_; lean_object* v_b_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_999_; 
v_x_975_ = lean_ctor_get(v_x_972_, 0);
v_ty_976_ = lean_ctor_get(v_x_972_, 1);
v_e_977_ = lean_ctor_get(v_x_972_, 2);
v_b_978_ = lean_ctor_get(v_x_972_, 3);
v_isSharedCheck_999_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_999_ == 0)
{
v___x_980_ = v_x_972_;
v_isShared_981_ = v_isSharedCheck_999_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_b_978_);
lean_inc(v_e_977_);
lean_inc(v_ty_976_);
lean_inc(v_x_975_);
lean_dec(v_x_972_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_999_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v_fst_986_; lean_object* v_snd_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_998_; 
v___x_982_ = lean_unsigned_to_nat(1u);
v___x_983_ = lean_nat_add(v_a_974_, v___x_982_);
lean_inc(v_a_973_);
lean_inc(v_a_974_);
v___x_984_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_x_975_, v_a_974_, v_a_973_);
v___x_985_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_978_, v___x_984_, v___x_983_);
lean_dec(v___x_984_);
v_fst_986_ = lean_ctor_get(v___x_985_, 0);
v_snd_987_ = lean_ctor_get(v___x_985_, 1);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_998_ == 0)
{
v___x_989_ = v___x_985_;
v_isShared_990_ = v_isSharedCheck_998_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_snd_987_);
lean_inc(v_fst_986_);
lean_dec(v___x_985_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_998_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = l_Lean_IR_NormalizeIds_normExpr(v_e_977_, v_a_973_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 3, v_fst_986_);
lean_ctor_set(v___x_980_, 2, v___x_991_);
lean_ctor_set(v___x_980_, 0, v_a_974_);
v___x_993_ = v___x_980_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_974_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_ty_976_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_997_, 3, v_fst_986_);
v___x_993_ = v_reuseFailAlloc_997_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_995_; 
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_993_);
v___x_995_ = v___x_989_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_snd_987_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
case 1:
{
lean_object* v_j_1000_; lean_object* v_xs_1001_; lean_object* v_v_1002_; lean_object* v_b_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1046_; 
v_j_1000_ = lean_ctor_get(v_x_972_, 0);
v_xs_1001_ = lean_ctor_get(v_x_972_, 1);
v_v_1002_ = lean_ctor_get(v_x_972_, 2);
v_b_1003_ = lean_ctor_get(v_x_972_, 3);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1005_ = v_x_972_;
v_isShared_1006_ = v_isSharedCheck_1046_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_b_1003_);
lean_inc(v_v_1002_);
lean_inc(v_xs_1001_);
lean_inc(v_j_1000_);
lean_dec(v_x_972_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1046_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v_fst_1008_; lean_object* v_snd_1009_; lean_object* v___y_1033_; lean_object* v___x_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___x_1036_ = lean_unsigned_to_nat(0u);
v___x_1037_ = lean_array_get_size(v_xs_1001_);
v___x_1038_ = lean_nat_dec_lt(v___x_1036_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_inc(v_a_973_);
v_fst_1008_ = v_a_973_;
v_snd_1009_ = v_a_974_;
goto v___jp_1007_;
}
else
{
uint8_t v___x_1039_; 
v___x_1039_ = lean_nat_dec_le(v___x_1037_, v___x_1037_);
if (v___x_1039_ == 0)
{
if (v___x_1038_ == 0)
{
lean_inc(v_a_973_);
v_fst_1008_ = v_a_973_;
v_snd_1009_ = v_a_974_;
goto v___jp_1007_;
}
else
{
size_t v___x_1040_; size_t v___x_1041_; lean_object* v___x_1042_; 
v___x_1040_ = ((size_t)0ULL);
v___x_1041_ = lean_usize_of_nat(v___x_1037_);
lean_inc(v_a_973_);
v___x_1042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_1001_, v___x_1040_, v___x_1041_, v_a_973_, v_a_974_);
v___y_1033_ = v___x_1042_;
goto v___jp_1032_;
}
}
else
{
size_t v___x_1043_; size_t v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = ((size_t)0ULL);
v___x_1044_ = lean_usize_of_nat(v___x_1037_);
lean_inc(v_a_973_);
v___x_1045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_1001_, v___x_1043_, v___x_1044_, v_a_973_, v_a_974_);
v___y_1033_ = v___x_1045_;
goto v___jp_1032_;
}
}
v___jp_1007_:
{
lean_object* v___x_1010_; lean_object* v_fst_1011_; lean_object* v_snd_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v_fst_1017_; lean_object* v_snd_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1031_; 
v___x_1010_ = l_Lean_IR_NormalizeIds_normFnBody(v_v_1002_, v_fst_1008_, v_snd_1009_);
v_fst_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_fst_1011_);
v_snd_1012_ = lean_ctor_get(v___x_1010_, 1);
lean_inc_n(v_snd_1012_, 2);
lean_dec_ref(v___x_1010_);
v___x_1013_ = lean_unsigned_to_nat(1u);
v___x_1014_ = lean_nat_add(v_snd_1012_, v___x_1013_);
lean_inc(v_a_973_);
v___x_1015_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_j_1000_, v_snd_1012_, v_a_973_);
v___x_1016_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1003_, v___x_1015_, v___x_1014_);
lean_dec(v___x_1015_);
v_fst_1017_ = lean_ctor_get(v___x_1016_, 0);
v_snd_1018_ = lean_ctor_get(v___x_1016_, 1);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1020_ = v___x_1016_;
v_isShared_1021_ = v_isSharedCheck_1031_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_snd_1018_);
lean_inc(v_fst_1017_);
lean_dec(v___x_1016_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1031_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
size_t v_sz_1022_; size_t v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v_sz_1022_ = lean_array_size(v_xs_1001_);
v___x_1023_ = ((size_t)0ULL);
v___x_1024_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(v_fst_1008_, v_sz_1022_, v___x_1023_, v_xs_1001_);
lean_dec(v_fst_1008_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 3, v_fst_1017_);
lean_ctor_set(v___x_1005_, 2, v_fst_1011_);
lean_ctor_set(v___x_1005_, 1, v___x_1024_);
lean_ctor_set(v___x_1005_, 0, v_snd_1012_);
v___x_1026_ = v___x_1005_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_snd_1012_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1030_, 2, v_fst_1011_);
lean_ctor_set(v_reuseFailAlloc_1030_, 3, v_fst_1017_);
v___x_1026_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1028_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v___x_1026_);
v___x_1028_ = v___x_1020_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_snd_1018_);
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
v___jp_1032_:
{
lean_object* v_fst_1034_; lean_object* v_snd_1035_; 
v_fst_1034_ = lean_ctor_get(v___y_1033_, 0);
lean_inc(v_fst_1034_);
v_snd_1035_ = lean_ctor_get(v___y_1033_, 1);
lean_inc(v_snd_1035_);
lean_dec_ref(v___y_1033_);
v_fst_1008_ = v_fst_1034_;
v_snd_1009_ = v_snd_1035_;
goto v___jp_1007_;
}
}
}
case 2:
{
lean_object* v_x_1047_; lean_object* v_i_1048_; lean_object* v_y_1049_; lean_object* v_b_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1069_; 
v_x_1047_ = lean_ctor_get(v_x_972_, 0);
v_i_1048_ = lean_ctor_get(v_x_972_, 1);
v_y_1049_ = lean_ctor_get(v_x_972_, 2);
v_b_1050_ = lean_ctor_get(v_x_972_, 3);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1052_ = v_x_972_;
v_isShared_1053_ = v_isSharedCheck_1069_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_b_1050_);
lean_inc(v_y_1049_);
lean_inc(v_i_1048_);
lean_inc(v_x_1047_);
lean_dec(v_x_972_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1069_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v_fst_1057_; lean_object* v_snd_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1068_; 
v___x_1054_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1047_, v_a_973_);
lean_dec(v_x_1047_);
v___x_1055_ = l_Lean_IR_NormalizeIds_normArg(v_y_1049_, v_a_973_);
v___x_1056_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1050_, v_a_973_, v_a_974_);
v_fst_1057_ = lean_ctor_get(v___x_1056_, 0);
v_snd_1058_ = lean_ctor_get(v___x_1056_, 1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1060_ = v___x_1056_;
v_isShared_1061_ = v_isSharedCheck_1068_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_snd_1058_);
lean_inc(v_fst_1057_);
lean_dec(v___x_1056_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1068_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 3, v_fst_1057_);
lean_ctor_set(v___x_1052_, 2, v___x_1055_);
lean_ctor_set(v___x_1052_, 0, v___x_1054_);
v___x_1063_ = v___x_1052_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_i_1048_);
lean_ctor_set(v_reuseFailAlloc_1067_, 2, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1067_, 3, v_fst_1057_);
v___x_1063_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1065_; 
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v___x_1063_);
v___x_1065_ = v___x_1060_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_snd_1058_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
case 3:
{
lean_object* v_x_1070_; lean_object* v_cidx_1071_; lean_object* v_b_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1090_; 
v_x_1070_ = lean_ctor_get(v_x_972_, 0);
v_cidx_1071_ = lean_ctor_get(v_x_972_, 1);
v_b_1072_ = lean_ctor_get(v_x_972_, 2);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1074_ = v_x_972_;
v_isShared_1075_ = v_isSharedCheck_1090_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_b_1072_);
lean_inc(v_cidx_1071_);
lean_inc(v_x_1070_);
lean_dec(v_x_972_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1090_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v_fst_1078_; lean_object* v_snd_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1089_; 
v___x_1076_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1070_, v_a_973_);
lean_dec(v_x_1070_);
v___x_1077_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1072_, v_a_973_, v_a_974_);
v_fst_1078_ = lean_ctor_get(v___x_1077_, 0);
v_snd_1079_ = lean_ctor_get(v___x_1077_, 1);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1081_ = v___x_1077_;
v_isShared_1082_ = v_isSharedCheck_1089_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_snd_1079_);
lean_inc(v_fst_1078_);
lean_dec(v___x_1077_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1089_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 2, v_fst_1078_);
lean_ctor_set(v___x_1074_, 0, v___x_1076_);
v___x_1084_ = v___x_1074_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_cidx_1071_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_fst_1078_);
v___x_1084_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1086_; 
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1084_);
v___x_1086_ = v___x_1081_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_snd_1079_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
case 4:
{
lean_object* v_x_1091_; lean_object* v_i_1092_; lean_object* v_y_1093_; lean_object* v_b_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1113_; 
v_x_1091_ = lean_ctor_get(v_x_972_, 0);
v_i_1092_ = lean_ctor_get(v_x_972_, 1);
v_y_1093_ = lean_ctor_get(v_x_972_, 2);
v_b_1094_ = lean_ctor_get(v_x_972_, 3);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1096_ = v_x_972_;
v_isShared_1097_ = v_isSharedCheck_1113_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_b_1094_);
lean_inc(v_y_1093_);
lean_inc(v_i_1092_);
lean_inc(v_x_1091_);
lean_dec(v_x_972_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1113_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v_fst_1101_; lean_object* v_snd_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1112_; 
v___x_1098_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1091_, v_a_973_);
lean_dec(v_x_1091_);
v___x_1099_ = l_Lean_IR_NormalizeIds_normIndex(v_y_1093_, v_a_973_);
lean_dec(v_y_1093_);
v___x_1100_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1094_, v_a_973_, v_a_974_);
v_fst_1101_ = lean_ctor_get(v___x_1100_, 0);
v_snd_1102_ = lean_ctor_get(v___x_1100_, 1);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1104_ = v___x_1100_;
v_isShared_1105_ = v_isSharedCheck_1112_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_snd_1102_);
lean_inc(v_fst_1101_);
lean_dec(v___x_1100_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1112_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 3, v_fst_1101_);
lean_ctor_set(v___x_1096_, 2, v___x_1099_);
lean_ctor_set(v___x_1096_, 0, v___x_1098_);
v___x_1107_ = v___x_1096_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_i_1092_);
lean_ctor_set(v_reuseFailAlloc_1111_, 2, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1111_, 3, v_fst_1101_);
v___x_1107_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1109_; 
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1107_);
v___x_1109_ = v___x_1104_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_snd_1102_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
case 5:
{
lean_object* v_x_1114_; lean_object* v_i_1115_; lean_object* v_offset_1116_; lean_object* v_y_1117_; lean_object* v_ty_1118_; lean_object* v_b_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1138_; 
v_x_1114_ = lean_ctor_get(v_x_972_, 0);
v_i_1115_ = lean_ctor_get(v_x_972_, 1);
v_offset_1116_ = lean_ctor_get(v_x_972_, 2);
v_y_1117_ = lean_ctor_get(v_x_972_, 3);
v_ty_1118_ = lean_ctor_get(v_x_972_, 4);
v_b_1119_ = lean_ctor_get(v_x_972_, 5);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1121_ = v_x_972_;
v_isShared_1122_ = v_isSharedCheck_1138_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_b_1119_);
lean_inc(v_ty_1118_);
lean_inc(v_y_1117_);
lean_inc(v_offset_1116_);
lean_inc(v_i_1115_);
lean_inc(v_x_1114_);
lean_dec(v_x_972_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1138_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v_fst_1126_; lean_object* v_snd_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1137_; 
v___x_1123_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1114_, v_a_973_);
lean_dec(v_x_1114_);
v___x_1124_ = l_Lean_IR_NormalizeIds_normIndex(v_y_1117_, v_a_973_);
lean_dec(v_y_1117_);
v___x_1125_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1119_, v_a_973_, v_a_974_);
v_fst_1126_ = lean_ctor_get(v___x_1125_, 0);
v_snd_1127_ = lean_ctor_get(v___x_1125_, 1);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1129_ = v___x_1125_;
v_isShared_1130_ = v_isSharedCheck_1137_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_snd_1127_);
lean_inc(v_fst_1126_);
lean_dec(v___x_1125_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1137_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 5, v_fst_1126_);
lean_ctor_set(v___x_1121_, 3, v___x_1124_);
lean_ctor_set(v___x_1121_, 0, v___x_1123_);
v___x_1132_ = v___x_1121_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_i_1115_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v_offset_1116_);
lean_ctor_set(v_reuseFailAlloc_1136_, 3, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1136_, 4, v_ty_1118_);
lean_ctor_set(v_reuseFailAlloc_1136_, 5, v_fst_1126_);
v___x_1132_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1134_; 
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1132_);
v___x_1134_ = v___x_1129_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_snd_1127_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
}
case 6:
{
lean_object* v_x_1139_; lean_object* v_n_1140_; uint8_t v_c_1141_; uint8_t v_persistent_1142_; lean_object* v_b_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1161_; 
v_x_1139_ = lean_ctor_get(v_x_972_, 0);
v_n_1140_ = lean_ctor_get(v_x_972_, 1);
v_c_1141_ = lean_ctor_get_uint8(v_x_972_, sizeof(void*)*3);
v_persistent_1142_ = lean_ctor_get_uint8(v_x_972_, sizeof(void*)*3 + 1);
v_b_1143_ = lean_ctor_get(v_x_972_, 2);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1145_ = v_x_972_;
v_isShared_1146_ = v_isSharedCheck_1161_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_b_1143_);
lean_inc(v_n_1140_);
lean_inc(v_x_1139_);
lean_dec(v_x_972_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1161_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v_fst_1149_; lean_object* v_snd_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1160_; 
v___x_1147_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1139_, v_a_973_);
lean_dec(v_x_1139_);
v___x_1148_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1143_, v_a_973_, v_a_974_);
v_fst_1149_ = lean_ctor_get(v___x_1148_, 0);
v_snd_1150_ = lean_ctor_get(v___x_1148_, 1);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1152_ = v___x_1148_;
v_isShared_1153_ = v_isSharedCheck_1160_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_snd_1150_);
lean_inc(v_fst_1149_);
lean_dec(v___x_1148_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1160_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 2, v_fst_1149_);
lean_ctor_set(v___x_1145_, 0, v___x_1147_);
v___x_1155_ = v___x_1145_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_n_1140_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_fst_1149_);
lean_ctor_set_uint8(v_reuseFailAlloc_1159_, sizeof(void*)*3, v_c_1141_);
lean_ctor_set_uint8(v_reuseFailAlloc_1159_, sizeof(void*)*3 + 1, v_persistent_1142_);
v___x_1155_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1157_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1155_);
v___x_1157_ = v___x_1152_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_snd_1150_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
case 7:
{
lean_object* v_x_1162_; lean_object* v_n_1163_; uint8_t v_c_1164_; uint8_t v_persistent_1165_; lean_object* v_b_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1184_; 
v_x_1162_ = lean_ctor_get(v_x_972_, 0);
v_n_1163_ = lean_ctor_get(v_x_972_, 1);
v_c_1164_ = lean_ctor_get_uint8(v_x_972_, sizeof(void*)*3);
v_persistent_1165_ = lean_ctor_get_uint8(v_x_972_, sizeof(void*)*3 + 1);
v_b_1166_ = lean_ctor_get(v_x_972_, 2);
v_isSharedCheck_1184_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1168_ = v_x_972_;
v_isShared_1169_ = v_isSharedCheck_1184_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_b_1166_);
lean_inc(v_n_1163_);
lean_inc(v_x_1162_);
lean_dec(v_x_972_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1184_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v_fst_1172_; lean_object* v_snd_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1183_; 
v___x_1170_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1162_, v_a_973_);
lean_dec(v_x_1162_);
v___x_1171_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1166_, v_a_973_, v_a_974_);
v_fst_1172_ = lean_ctor_get(v___x_1171_, 0);
v_snd_1173_ = lean_ctor_get(v___x_1171_, 1);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1175_ = v___x_1171_;
v_isShared_1176_ = v_isSharedCheck_1183_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_snd_1173_);
lean_inc(v_fst_1172_);
lean_dec(v___x_1171_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1183_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 2, v_fst_1172_);
lean_ctor_set(v___x_1168_, 0, v___x_1170_);
v___x_1178_ = v___x_1168_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_n_1163_);
lean_ctor_set(v_reuseFailAlloc_1182_, 2, v_fst_1172_);
lean_ctor_set_uint8(v_reuseFailAlloc_1182_, sizeof(void*)*3, v_c_1164_);
lean_ctor_set_uint8(v_reuseFailAlloc_1182_, sizeof(void*)*3 + 1, v_persistent_1165_);
v___x_1178_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1180_; 
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 0, v___x_1178_);
v___x_1180_ = v___x_1175_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_snd_1173_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
case 8:
{
lean_object* v_x_1185_; lean_object* v_b_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1204_; 
v_x_1185_ = lean_ctor_get(v_x_972_, 0);
v_b_1186_ = lean_ctor_get(v_x_972_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1188_ = v_x_972_;
v_isShared_1189_ = v_isSharedCheck_1204_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_b_1186_);
lean_inc(v_x_1185_);
lean_dec(v_x_972_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1204_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v_fst_1192_; lean_object* v_snd_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1203_; 
v___x_1190_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1185_, v_a_973_);
lean_dec(v_x_1185_);
v___x_1191_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1186_, v_a_973_, v_a_974_);
v_fst_1192_ = lean_ctor_get(v___x_1191_, 0);
v_snd_1193_ = lean_ctor_get(v___x_1191_, 1);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1195_ = v___x_1191_;
v_isShared_1196_ = v_isSharedCheck_1203_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_snd_1193_);
lean_inc(v_fst_1192_);
lean_dec(v___x_1191_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1203_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 1, v_fst_1192_);
lean_ctor_set(v___x_1188_, 0, v___x_1190_);
v___x_1198_ = v___x_1188_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_fst_1192_);
v___x_1198_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1200_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1198_);
v___x_1200_ = v___x_1195_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_snd_1193_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
case 9:
{
lean_object* v_tid_1205_; lean_object* v_x_1206_; lean_object* v_xType_1207_; lean_object* v_cs_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1228_; 
v_tid_1205_ = lean_ctor_get(v_x_972_, 0);
v_x_1206_ = lean_ctor_get(v_x_972_, 1);
v_xType_1207_ = lean_ctor_get(v_x_972_, 2);
v_cs_1208_ = lean_ctor_get(v_x_972_, 3);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1210_ = v_x_972_;
v_isShared_1211_ = v_isSharedCheck_1228_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_cs_1208_);
lean_inc(v_xType_1207_);
lean_inc(v_x_1206_);
lean_inc(v_tid_1205_);
lean_dec(v_x_972_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1228_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; size_t v_sz_1213_; size_t v___x_1214_; lean_object* v___x_1215_; lean_object* v_fst_1216_; lean_object* v_snd_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1227_; 
v___x_1212_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1206_, v_a_973_);
lean_dec(v_x_1206_);
v_sz_1213_ = lean_array_size(v_cs_1208_);
v___x_1214_ = ((size_t)0ULL);
v___x_1215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(v_sz_1213_, v___x_1214_, v_cs_1208_, v_a_973_, v_a_974_);
v_fst_1216_ = lean_ctor_get(v___x_1215_, 0);
v_snd_1217_ = lean_ctor_get(v___x_1215_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1219_ = v___x_1215_;
v_isShared_1220_ = v_isSharedCheck_1227_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_snd_1217_);
lean_inc(v_fst_1216_);
lean_dec(v___x_1215_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1227_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 3, v_fst_1216_);
lean_ctor_set(v___x_1210_, 1, v___x_1212_);
v___x_1222_ = v___x_1210_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_tid_1205_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_xType_1207_);
lean_ctor_set(v_reuseFailAlloc_1226_, 3, v_fst_1216_);
v___x_1222_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1224_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1222_);
v___x_1224_ = v___x_1219_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_snd_1217_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
case 10:
{
lean_object* v_x_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1238_; 
v_x_1229_ = lean_ctor_get(v_x_972_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1231_ = v_x_972_;
v_isShared_1232_ = v_isSharedCheck_1238_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_x_1229_);
lean_dec(v_x_972_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1238_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1233_ = l_Lean_IR_NormalizeIds_normArg(v_x_1229_, v_a_973_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1233_);
v___x_1235_ = v___x_1231_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1236_; 
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
lean_ctor_set(v___x_1236_, 1, v_a_974_);
return v___x_1236_;
}
}
}
case 11:
{
lean_object* v_j_1239_; lean_object* v_ys_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1250_; 
v_j_1239_ = lean_ctor_get(v_x_972_, 0);
v_ys_1240_ = lean_ctor_get(v_x_972_, 1);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1242_ = v_x_972_;
v_isShared_1243_ = v_isSharedCheck_1250_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_ys_1240_);
lean_inc(v_j_1239_);
lean_dec(v_x_972_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1250_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___x_1244_ = l_Lean_IR_NormalizeIds_normIndex(v_j_1239_, v_a_973_);
lean_dec(v_j_1239_);
v___x_1245_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_1240_, v_a_973_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v___x_1245_);
lean_ctor_set(v___x_1242_, 0, v___x_1244_);
v___x_1247_ = v___x_1242_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1244_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
lean_ctor_set(v___x_1248_, 1, v_a_974_);
return v___x_1248_;
}
}
}
default: 
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v_x_972_);
lean_ctor_set(v___x_1251_, 1, v_a_974_);
return v___x_1251_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(size_t v_sz_1252_, size_t v_i_1253_, lean_object* v_bs_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
uint8_t v___x_1257_; 
v___x_1257_ = lean_usize_dec_lt(v_i_1253_, v_sz_1252_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; 
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v_bs_1254_);
lean_ctor_set(v___x_1258_, 1, v___y_1256_);
return v___x_1258_;
}
else
{
lean_object* v_v_1259_; lean_object* v___x_1260_; lean_object* v_bs_x27_1261_; lean_object* v_fst_1263_; lean_object* v_snd_1264_; 
v_v_1259_ = lean_array_uget(v_bs_1254_, v_i_1253_);
v___x_1260_ = lean_unsigned_to_nat(0u);
v_bs_x27_1261_ = lean_array_uset(v_bs_1254_, v_i_1253_, v___x_1260_);
if (lean_obj_tag(v_v_1259_) == 0)
{
lean_object* v_info_1269_; lean_object* v_b_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1280_; 
v_info_1269_ = lean_ctor_get(v_v_1259_, 0);
v_b_1270_ = lean_ctor_get(v_v_1259_, 1);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_v_1259_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1272_ = v_v_1259_;
v_isShared_1273_ = v_isSharedCheck_1280_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_b_1270_);
lean_inc(v_info_1269_);
lean_dec(v_v_1259_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1280_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v_fst_1275_; lean_object* v_snd_1276_; lean_object* v___x_1278_; 
v___x_1274_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1270_, v___y_1255_, v___y_1256_);
v_fst_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_fst_1275_);
v_snd_1276_ = lean_ctor_get(v___x_1274_, 1);
lean_inc(v_snd_1276_);
lean_dec_ref(v___x_1274_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 1, v_fst_1275_);
v___x_1278_ = v___x_1272_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_info_1269_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_fst_1275_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
v_fst_1263_ = v___x_1278_;
v_snd_1264_ = v_snd_1276_;
goto v___jp_1262_;
}
}
}
else
{
lean_object* v_b_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1291_; 
v_b_1281_ = lean_ctor_get(v_v_1259_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_v_1259_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1283_ = v_v_1259_;
v_isShared_1284_ = v_isSharedCheck_1291_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_b_1281_);
lean_dec(v_v_1259_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1291_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v_fst_1286_; lean_object* v_snd_1287_; lean_object* v___x_1289_; 
v___x_1285_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1281_, v___y_1255_, v___y_1256_);
v_fst_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_fst_1286_);
v_snd_1287_ = lean_ctor_get(v___x_1285_, 1);
lean_inc(v_snd_1287_);
lean_dec_ref(v___x_1285_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v_fst_1286_);
v___x_1289_ = v___x_1283_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_fst_1286_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
v_fst_1263_ = v___x_1289_;
v_snd_1264_ = v_snd_1287_;
goto v___jp_1262_;
}
}
}
v___jp_1262_:
{
size_t v___x_1265_; size_t v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = ((size_t)1ULL);
v___x_1266_ = lean_usize_add(v_i_1253_, v___x_1265_);
v___x_1267_ = lean_array_uset(v_bs_x27_1261_, v_i_1253_, v_fst_1263_);
v_i_1253_ = v___x_1266_;
v_bs_1254_ = v___x_1267_;
v___y_1256_ = v_snd_1264_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2___boxed(lean_object* v_sz_1292_, lean_object* v_i_1293_, lean_object* v_bs_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
size_t v_sz_boxed_1297_; size_t v_i_boxed_1298_; lean_object* v_res_1299_; 
v_sz_boxed_1297_ = lean_unbox_usize(v_sz_1292_);
lean_dec(v_sz_1292_);
v_i_boxed_1298_ = lean_unbox_usize(v_i_1293_);
lean_dec(v_i_1293_);
v_res_1299_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(v_sz_boxed_1297_, v_i_boxed_1298_, v_bs_1294_, v___y_1295_, v___y_1296_);
lean_dec(v___y_1295_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normFnBody___boxed(lean_object* v_x_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_IR_NormalizeIds_normFnBody(v_x_1300_, v_a_1301_, v_a_1302_);
lean_dec(v_a_1301_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normDecl(lean_object* v_d_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
if (lean_obj_tag(v_d_1304_) == 0)
{
lean_object* v_xs_1307_; lean_object* v_body_1308_; lean_object* v_fst_1310_; lean_object* v_snd_1311_; lean_object* v___y_1324_; lean_object* v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v_xs_1307_ = lean_ctor_get(v_d_1304_, 1);
v_body_1308_ = lean_ctor_get(v_d_1304_, 3);
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = lean_array_get_size(v_xs_1307_);
v___x_1329_ = lean_nat_dec_lt(v___x_1327_, v___x_1328_);
if (v___x_1329_ == 0)
{
lean_inc(v_a_1305_);
v_fst_1310_ = v_a_1305_;
v_snd_1311_ = v_a_1306_;
goto v___jp_1309_;
}
else
{
uint8_t v___x_1330_; 
v___x_1330_ = lean_nat_dec_le(v___x_1328_, v___x_1328_);
if (v___x_1330_ == 0)
{
if (v___x_1329_ == 0)
{
lean_inc(v_a_1305_);
v_fst_1310_ = v_a_1305_;
v_snd_1311_ = v_a_1306_;
goto v___jp_1309_;
}
else
{
size_t v___x_1331_; size_t v___x_1332_; lean_object* v___x_1333_; 
v___x_1331_ = ((size_t)0ULL);
v___x_1332_ = lean_usize_of_nat(v___x_1328_);
lean_inc(v_a_1305_);
v___x_1333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_1307_, v___x_1331_, v___x_1332_, v_a_1305_, v_a_1306_);
v___y_1324_ = v___x_1333_;
goto v___jp_1323_;
}
}
else
{
size_t v___x_1334_; size_t v___x_1335_; lean_object* v___x_1336_; 
v___x_1334_ = ((size_t)0ULL);
v___x_1335_ = lean_usize_of_nat(v___x_1328_);
lean_inc(v_a_1305_);
v___x_1336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_1307_, v___x_1334_, v___x_1335_, v_a_1305_, v_a_1306_);
v___y_1324_ = v___x_1336_;
goto v___jp_1323_;
}
}
v___jp_1309_:
{
lean_object* v___x_1312_; lean_object* v_fst_1313_; lean_object* v_snd_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1322_; 
lean_inc(v_body_1308_);
v___x_1312_ = l_Lean_IR_NormalizeIds_normFnBody(v_body_1308_, v_fst_1310_, v_snd_1311_);
lean_dec(v_fst_1310_);
v_fst_1313_ = lean_ctor_get(v___x_1312_, 0);
v_snd_1314_ = lean_ctor_get(v___x_1312_, 1);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1316_ = v___x_1312_;
v_isShared_1317_ = v_isSharedCheck_1322_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_snd_1314_);
lean_inc(v_fst_1313_);
lean_dec(v___x_1312_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1322_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; lean_object* v___x_1320_; 
v___x_1318_ = l_Lean_IR_Decl_updateBody_x21(v_d_1304_, v_fst_1313_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v___x_1318_);
v___x_1320_ = v___x_1316_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1318_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_snd_1314_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
v___jp_1323_:
{
lean_object* v_fst_1325_; lean_object* v_snd_1326_; 
v_fst_1325_ = lean_ctor_get(v___y_1324_, 0);
lean_inc(v_fst_1325_);
v_snd_1326_ = lean_ctor_get(v___y_1324_, 1);
lean_inc(v_snd_1326_);
lean_dec_ref(v___y_1324_);
v_fst_1310_ = v_fst_1325_;
v_snd_1311_ = v_snd_1326_;
goto v___jp_1309_;
}
}
else
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1337_, 0, v_d_1304_);
lean_ctor_set(v___x_1337_, 1, v_a_1306_);
return v___x_1337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normDecl___boxed(lean_object* v_d_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_IR_NormalizeIds_normDecl(v_d_1338_, v_a_1339_, v_a_1340_);
lean_dec(v_a_1339_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_normalizeIds(lean_object* v_d_1342_){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v_fst_1346_; 
v___x_1343_ = lean_box(1);
v___x_1344_ = lean_unsigned_to_nat(1u);
v___x_1345_ = l_Lean_IR_NormalizeIds_normDecl(v_d_1342_, v___x_1343_, v___x_1344_);
v_fst_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_fst_1346_);
lean_dec_ref(v___x_1345_);
return v_fst_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArg(lean_object* v_f_1347_, lean_object* v_x_1348_){
_start:
{
if (lean_obj_tag(v_x_1348_) == 0)
{
lean_object* v_id_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1357_; 
v_id_1349_ = lean_ctor_get(v_x_1348_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_x_1348_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1351_ = v_x_1348_;
v_isShared_1352_ = v_isSharedCheck_1357_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_id_1349_);
lean_dec(v_x_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1357_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1353_ = lean_apply_1(v_f_1347_, v_id_1349_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v___x_1353_);
v___x_1355_ = v___x_1351_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
else
{
lean_dec_ref(v_f_1347_);
return v_x_1348_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(lean_object* v_f_1358_, size_t v_sz_1359_, size_t v_i_1360_, lean_object* v_bs_1361_){
_start:
{
uint8_t v___x_1362_; 
v___x_1362_ = lean_usize_dec_lt(v_i_1360_, v_sz_1359_);
if (v___x_1362_ == 0)
{
lean_dec_ref(v_f_1358_);
return v_bs_1361_;
}
else
{
lean_object* v_v_1363_; lean_object* v___x_1364_; lean_object* v_bs_x27_1365_; lean_object* v___y_1367_; 
v_v_1363_ = lean_array_uget(v_bs_1361_, v_i_1360_);
v___x_1364_ = lean_unsigned_to_nat(0u);
v_bs_x27_1365_ = lean_array_uset(v_bs_1361_, v_i_1360_, v___x_1364_);
if (lean_obj_tag(v_v_1363_) == 0)
{
lean_object* v_id_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1380_; 
v_id_1372_ = lean_ctor_get(v_v_1363_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_v_1363_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1374_ = v_v_1363_;
v_isShared_1375_ = v_isSharedCheck_1380_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_id_1372_);
lean_dec(v_v_1363_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1380_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1378_; 
lean_inc_ref(v_f_1358_);
v___x_1376_ = lean_apply_1(v_f_1358_, v_id_1372_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v___x_1376_);
v___x_1378_ = v___x_1374_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
v___y_1367_ = v___x_1378_;
goto v___jp_1366_;
}
}
}
else
{
v___y_1367_ = v_v_1363_;
goto v___jp_1366_;
}
v___jp_1366_:
{
size_t v___x_1368_; size_t v___x_1369_; lean_object* v___x_1370_; 
v___x_1368_ = ((size_t)1ULL);
v___x_1369_ = lean_usize_add(v_i_1360_, v___x_1368_);
v___x_1370_ = lean_array_uset(v_bs_x27_1365_, v_i_1360_, v___y_1367_);
v_i_1360_ = v___x_1369_;
v_bs_1361_ = v___x_1370_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0___boxed(lean_object* v_f_1381_, lean_object* v_sz_1382_, lean_object* v_i_1383_, lean_object* v_bs_1384_){
_start:
{
size_t v_sz_boxed_1385_; size_t v_i_boxed_1386_; lean_object* v_res_1387_; 
v_sz_boxed_1385_ = lean_unbox_usize(v_sz_1382_);
lean_dec(v_sz_1382_);
v_i_boxed_1386_ = lean_unbox_usize(v_i_1383_);
lean_dec(v_i_1383_);
v_res_1387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(v_f_1381_, v_sz_boxed_1385_, v_i_boxed_1386_, v_bs_1384_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArgs(lean_object* v_f_1388_, lean_object* v_as_1389_){
_start:
{
size_t v_sz_1390_; size_t v___x_1391_; lean_object* v___x_1392_; 
v_sz_1390_ = lean_array_size(v_as_1389_);
v___x_1391_ = ((size_t)0ULL);
v___x_1392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(v_f_1388_, v_sz_1390_, v___x_1391_, v_as_1389_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapExpr(lean_object* v_f_1393_, lean_object* v_x_1394_){
_start:
{
switch(lean_obj_tag(v_x_1394_))
{
case 0:
{
lean_object* v_i_1395_; lean_object* v_ys_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1404_; 
v_i_1395_ = lean_ctor_get(v_x_1394_, 0);
v_ys_1396_ = lean_ctor_get(v_x_1394_, 1);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1398_ = v_x_1394_;
v_isShared_1399_ = v_isSharedCheck_1404_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_ys_1396_);
lean_inc(v_i_1395_);
lean_dec(v_x_1394_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1404_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1400_ = l_Lean_IR_MapVars_mapArgs(v_f_1393_, v_ys_1396_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 1, v___x_1400_);
v___x_1402_ = v___x_1398_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_i_1395_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
case 1:
{
lean_object* v_n_1405_; lean_object* v_x_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1414_; 
v_n_1405_ = lean_ctor_get(v_x_1394_, 0);
v_x_1406_ = lean_ctor_get(v_x_1394_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1408_ = v_x_1394_;
v_isShared_1409_ = v_isSharedCheck_1414_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_x_1406_);
lean_inc(v_n_1405_);
lean_dec(v_x_1394_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1414_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1410_ = lean_apply_1(v_f_1393_, v_x_1406_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 1, v___x_1410_);
v___x_1412_ = v___x_1408_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_n_1405_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
case 2:
{
lean_object* v_x_1415_; lean_object* v_i_1416_; uint8_t v_updtHeader_1417_; lean_object* v_ys_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1427_; 
v_x_1415_ = lean_ctor_get(v_x_1394_, 0);
v_i_1416_ = lean_ctor_get(v_x_1394_, 1);
v_updtHeader_1417_ = lean_ctor_get_uint8(v_x_1394_, sizeof(void*)*3);
v_ys_1418_ = lean_ctor_get(v_x_1394_, 2);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1420_ = v_x_1394_;
v_isShared_1421_ = v_isSharedCheck_1427_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_ys_1418_);
lean_inc(v_i_1416_);
lean_inc(v_x_1415_);
lean_dec(v_x_1394_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1427_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1425_; 
lean_inc_ref(v_f_1393_);
v___x_1422_ = lean_apply_1(v_f_1393_, v_x_1415_);
v___x_1423_ = l_Lean_IR_MapVars_mapArgs(v_f_1393_, v_ys_1418_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 2, v___x_1423_);
lean_ctor_set(v___x_1420_, 0, v___x_1422_);
v___x_1425_ = v___x_1420_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_i_1416_);
lean_ctor_set(v_reuseFailAlloc_1426_, 2, v___x_1423_);
lean_ctor_set_uint8(v_reuseFailAlloc_1426_, sizeof(void*)*3, v_updtHeader_1417_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
case 3:
{
lean_object* v_i_1428_; lean_object* v_x_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1437_; 
v_i_1428_ = lean_ctor_get(v_x_1394_, 0);
v_x_1429_ = lean_ctor_get(v_x_1394_, 1);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1431_ = v_x_1394_;
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_x_1429_);
lean_inc(v_i_1428_);
lean_dec(v_x_1394_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1433_ = lean_apply_1(v_f_1393_, v_x_1429_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v___x_1433_);
v___x_1435_ = v___x_1431_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_i_1428_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
case 4:
{
lean_object* v_i_1438_; lean_object* v_x_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1447_; 
v_i_1438_ = lean_ctor_get(v_x_1394_, 0);
v_x_1439_ = lean_ctor_get(v_x_1394_, 1);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1441_ = v_x_1394_;
v_isShared_1442_ = v_isSharedCheck_1447_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_x_1439_);
lean_inc(v_i_1438_);
lean_dec(v_x_1394_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1447_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1443_ = lean_apply_1(v_f_1393_, v_x_1439_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 1, v___x_1443_);
v___x_1445_ = v___x_1441_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_i_1438_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
case 5:
{
lean_object* v_n_1448_; lean_object* v_offset_1449_; lean_object* v_x_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1458_; 
v_n_1448_ = lean_ctor_get(v_x_1394_, 0);
v_offset_1449_ = lean_ctor_get(v_x_1394_, 1);
v_x_1450_ = lean_ctor_get(v_x_1394_, 2);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1452_ = v_x_1394_;
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_x_1450_);
lean_inc(v_offset_1449_);
lean_inc(v_n_1448_);
lean_dec(v_x_1394_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1454_ = lean_apply_1(v_f_1393_, v_x_1450_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 2, v___x_1454_);
v___x_1456_ = v___x_1452_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_n_1448_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_offset_1449_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
case 6:
{
lean_object* v_c_1459_; lean_object* v_ys_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1468_; 
v_c_1459_ = lean_ctor_get(v_x_1394_, 0);
v_ys_1460_ = lean_ctor_get(v_x_1394_, 1);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1462_ = v_x_1394_;
v_isShared_1463_ = v_isSharedCheck_1468_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_ys_1460_);
lean_inc(v_c_1459_);
lean_dec(v_x_1394_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1468_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1464_ = l_Lean_IR_MapVars_mapArgs(v_f_1393_, v_ys_1460_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 1, v___x_1464_);
v___x_1466_ = v___x_1462_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_c_1459_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
case 7:
{
lean_object* v_c_1469_; lean_object* v_ys_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1478_; 
v_c_1469_ = lean_ctor_get(v_x_1394_, 0);
v_ys_1470_ = lean_ctor_get(v_x_1394_, 1);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1472_ = v_x_1394_;
v_isShared_1473_ = v_isSharedCheck_1478_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_ys_1470_);
lean_inc(v_c_1469_);
lean_dec(v_x_1394_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1478_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1474_ = l_Lean_IR_MapVars_mapArgs(v_f_1393_, v_ys_1470_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 1, v___x_1474_);
v___x_1476_ = v___x_1472_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_c_1469_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
case 8:
{
lean_object* v_x_1479_; lean_object* v_ys_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1489_; 
v_x_1479_ = lean_ctor_get(v_x_1394_, 0);
v_ys_1480_ = lean_ctor_get(v_x_1394_, 1);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1482_ = v_x_1394_;
v_isShared_1483_ = v_isSharedCheck_1489_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_ys_1480_);
lean_inc(v_x_1479_);
lean_dec(v_x_1394_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1489_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
lean_inc_ref(v_f_1393_);
v___x_1484_ = lean_apply_1(v_f_1393_, v_x_1479_);
v___x_1485_ = l_Lean_IR_MapVars_mapArgs(v_f_1393_, v_ys_1480_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 1, v___x_1485_);
lean_ctor_set(v___x_1482_, 0, v___x_1484_);
v___x_1487_ = v___x_1482_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
case 9:
{
lean_object* v_ty_1490_; lean_object* v_x_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1499_; 
v_ty_1490_ = lean_ctor_get(v_x_1394_, 0);
v_x_1491_ = lean_ctor_get(v_x_1394_, 1);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1493_ = v_x_1394_;
v_isShared_1494_ = v_isSharedCheck_1499_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_x_1491_);
lean_inc(v_ty_1490_);
lean_dec(v_x_1394_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1499_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1495_ = lean_apply_1(v_f_1393_, v_x_1491_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 1, v___x_1495_);
v___x_1497_ = v___x_1493_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_ty_1490_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
case 10:
{
lean_object* v_x_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1508_; 
v_x_1500_ = lean_ctor_get(v_x_1394_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1502_ = v_x_1394_;
v_isShared_1503_ = v_isSharedCheck_1508_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_x_1500_);
lean_dec(v_x_1394_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1508_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1504_ = lean_apply_1(v_f_1393_, v_x_1500_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v___x_1504_);
v___x_1506_ = v___x_1502_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
case 11:
{
lean_dec_ref(v_f_1393_);
return v_x_1394_;
}
default: 
{
lean_object* v_x_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1517_; 
v_x_1509_ = lean_ctor_get(v_x_1394_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1511_ = v_x_1394_;
v_isShared_1512_ = v_isSharedCheck_1517_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_x_1509_);
lean_dec(v_x_1394_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1517_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1513_ = lean_apply_1(v_f_1393_, v_x_1509_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v___x_1513_);
v___x_1515_ = v___x_1511_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapFnBody(lean_object* v_f_1518_, lean_object* v_x_1519_){
_start:
{
switch(lean_obj_tag(v_x_1519_))
{
case 0:
{
lean_object* v_x_1520_; lean_object* v_ty_1521_; lean_object* v_e_1522_; lean_object* v_b_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1532_; 
v_x_1520_ = lean_ctor_get(v_x_1519_, 0);
v_ty_1521_ = lean_ctor_get(v_x_1519_, 1);
v_e_1522_ = lean_ctor_get(v_x_1519_, 2);
v_b_1523_ = lean_ctor_get(v_x_1519_, 3);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_x_1519_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1525_ = v_x_1519_;
v_isShared_1526_ = v_isSharedCheck_1532_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_b_1523_);
lean_inc(v_e_1522_);
lean_inc(v_ty_1521_);
lean_inc(v_x_1520_);
lean_dec(v_x_1519_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1532_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; 
lean_inc_ref(v_f_1518_);
v___x_1527_ = l_Lean_IR_MapVars_mapExpr(v_f_1518_, v_e_1522_);
v___x_1528_ = l_Lean_IR_MapVars_mapFnBody(v_f_1518_, v_b_1523_);
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
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_x_1520_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_ty_1521_);
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
case 1:
{
lean_object* v_j_1533_; lean_object* v_xs_1534_; lean_object* v_v_1535_; lean_object* v_b_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1545_; 
v_j_1533_ = lean_ctor_get(v_x_1519_, 0);
v_xs_1534_ = lean_ctor_get(v_x_1519_, 1);
v_v_1535_ = lean_ctor_get(v_x_1519_, 2);
v_b_1536_ = lean_ctor_get(v_x_1519_, 3);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_x_1519_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1538_ = v_x_1519_;
v_isShared_1539_ = v_isSharedCheck_1545_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_b_1536_);
lean_inc(v_v_1535_);
lean_inc(v_xs_1534_);
lean_inc(v_j_1533_);
lean_dec(v_x_1519_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1545_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
lean_inc_ref(v_f_1518_);
v___x_1540_ = l_Lean_IR_MapVars_mapFnBody(v_f_1518_, v_v_1535_);
v___x_1541_ = l_Lean_IR_MapVars_mapFnBody(v_f_1518_, v_b_1536_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 3, v___x_1541_);
lean_ctor_set(v___x_1538_, 2, v___x_1540_);
v___x_1543_ = v___x_1538_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_j_1533_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_xs_1534_);
lean_ctor_set(v_reuseFailAlloc_1544_, 2, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1544_, 3, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
case 2:
{
lean_object* v_x_1546_; lean_object* v_i_1547_; lean_object* v_y_1548_; lean_object* v_b_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1569_; 
v_x_1546_ = lean_ctor_get(v_x_1519_, 0);
v_i_1547_ = lean_ctor_get(v_x_1519_, 1);
v_y_1548_ = lean_ctor_get(v_x_1519_, 2);
v_b_1549_ = lean_ctor_get(v_x_1519_, 3);
v_isSharedCheck_1569_ = !lean_is_exclusive(v_x_1519_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1551_ = v_x_1519_;
v_isShared_1552_ = v_isSharedCheck_1569_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_b_1549_);
lean_inc(v_y_1548_);
lean_inc(v_i_1547_);
lean_inc(v_x_1546_);
lean_dec(v_x_1519_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1569_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; lean_object* v___y_1555_; 
lean_inc_ref(v_f_1518_);
v___x_1553_ = lean_apply_1(v_f_1518_, v_x_1546_);
if (lean_obj_tag(v_y_1548_) == 0)
{
lean_object* v_id_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1568_; 
v_id_1560_ = lean_ctor_get(v_y_1548_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_y_1548_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1562_ = v_y_1548_;
v_isShared_1563_ = v_isSharedCheck_1568_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_id_1560_);
lean_dec(v_y_1548_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1568_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1566_; 
lean_inc_ref(v_f_1518_);
v___x_1564_ = lean_apply_1(v_f_1518_, v_id_1560_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1564_);
v___x_1566_ = v___x_1562_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
v___y_1555_ = v___x_1566_;
goto v___jp_1554_;
}
}
}
else
{
v___y_1555_ = v_y_1548_;
goto v___jp_1554_;
}
v___jp_1554_:
{
lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1556_ = l_Lean_IR_MapVars_mapFnBody(v_f_1518_, v_b_1549_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 3, v___x_1556_);
lean_ctor_set(v___x_1551_, 2, v___y_1555_);
lean_ctor_set(v___x_1551_, 0, v___x_1553_);
v___x_1558_ = v___x_1551_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_i_1547_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v___y_1555_);
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
}
case 3:
{
lean_object* v_x_1570_; lean_object* v_cidx_1571_; lean_object* v_b_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1581_; 
v_x_1570_ = lean_ctor_get(v_x_1519_, 0);
v_cidx_1571_ = lean_ctor_get(v_x_1519_, 1);
v_b_1572_ = lean_ctor_get(v_x_1519_, 2);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_x_1519_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1574_ = v_x_1519_;
v_isShared_1575_ = v_isSharedCheck_1581_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_b_1572_);
lean_inc(v_cidx_1571_);
lean_inc(v_x_1570_);
lean_dec(v_x_1519_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1581_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1579_; 
lean_inc_ref(v_f_1518_);
v___x_1576_ = lean_apply_1(v_f_1518_, v_x_1570_);
v___x_1577_ = l_Lean_IR_MapVars_mapFnBody(v_f_1518_, v_b_1572_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 2, v___x_1577_);
lean_ctor_set(v___x_1574_, 0, v___x_1576_);
v___x_1579_ = v___x_1574_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_cidx_1571_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
case 4:
{
lean_object* v_x_1582_; lean_object* v_i_1583_; lean_object* v_y_1584_; lean_object* v_b_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1595_; 
v_x_1582_ = lean_ctor_get(v_x_1519_, 0);
v_i_1583_ = lean_ctor_get(v_x_1519_, 1);
v_y_1584_ = lean_ctor_get(v_x_1519_, 2);
v_b_1585_ = lean_ctor_get(v_x_1519_, 3);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_x_1519_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1587_ = v_x_1519_;
v_isShared_1588_ = v_isSharedCheck_1595_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_b_1585_);
lean_inc(v_y_1584_);
lean_inc(v_i_1583_);
lean_inc(v_x_1582_);
lean_dec(v_x_1519_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1595_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
lean_inc_ref_n(v_f_1518_, 2);
v___x_1589_ = lean_apply_1(v_f_1518_, v_x_1582_);
v___x_1590_ = lean_apply_1(v_f_1518_, v_y_1584_);
v___x_1591_ = l_Lean_IR_MapVars_mapFnBody(v_f_1518_, v_b_1585_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 3, v___x_1591_);
lean_ctor_set(v___x_1587_, 2, v___x_1590_);
lean_ctor_set(v___x_1587_, 0, v___x_1589_);
v___x_1593_ = v___x_1587_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_i_1583_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1594_, 3, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
case 5:
{
lean_object* v_x_1596_; lean_object* v_i_1597_; lean_object* v_offset_1598_; lean_object* v_y_1599_; lean_object* v_ty_1600_; lean_object* v_b_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1611_; 
v_x_1596_ = lean_ctor_get(v_x_1519_, 0);
v_i_1597_ = lean_ctor_get(v_x_1519_, 1);
v_offset_1598_ = lean_ctor_get(v_x_1519_, 2);
v_y_1599_ = lean_ctor_get(v_x_1519_, 3);
v_ty_1600_ = lean_ctor_get(v_x_1519_, 4);
v_b_1601_ = lean_ctor_get(v_x_1519_, 5);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_x_1519_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1603_ = v_x_1519_;
v_isShared_1604_ = v_isSharedCheck_1611_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_b_1601_);
lean_inc(v_ty_1600_);
lean_inc(v_y_1599_);
lean_inc(v_offset_1598_);
lean_inc(v_i_1597_);
lean_inc(v_x_1596_);
lean_dec(v_x_1519_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1611_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1609_; 
lean_inc_ref_n(v_f_1518_, 2);
v___x_1605_ = lean_apply_1(v_f_1518_, v_x_1596_);
v___x_1606_ = lean_apply_1(v_f_1518_, v_y_1599_);
v___x_1607_ = l_Lean_IR_MapVars_mapFnBody(v_f_1518_, v_b_1601_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 5, v___x_1607_);
lean_ctor_set(v___x_1603_, 3, v___x_1606_);
lean_ctor_set(v___x_1603_, 0, v___x_1605_);
v___x_1609_ = v___x_1603_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_i_1597_);
lean_ctor_set(v_reuseFailAlloc_1610_, 2, v_offset_1598_);
lean_ctor_set(v_reuseFailAlloc_1610_, 3, v___x_1606_);
lean_ctor_set(v_reuseFailAlloc_1610_, 4, v_ty_1600_);
lean_ctor_set(v_reuseFailAlloc_1610_, 5, v___x_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
case 6:
{
lean_object* v_x_1612_; lean_object* v_n_1613_; uint8_t v_c_1614_; uint8_t v_persistent_1615_; lean_object* v_b_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1625_; 
v_x_1612_ = lean_ctor_get(v_x_1519_, 0);
v_n_1613_ = lean_ctor_get(v_x_1519_, 1);
v_c_1614_ = lean_ctor_get_uint8(v_x_1519_, sizeof(void*)*3);
v_persistent_1615_ = lean_ctor_get_uint8(v_x_1519_, sizeof(void*)*3 + 1);
v_b_1616_ = lean_ctor_get(v_x_1519_, 2);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_x_1519_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1618_ = v_x_1519_;
v_isShared_1619_ = v_isSharedCheck_1625_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_b_1616_);
lean_inc(v_n_1613_);
lean_inc(v_x_1612_);
lean_dec(v_x_1519_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1625_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
lean_inc_ref(v_f_1518_);
v___x_1620_ = lean_apply_1(v_f_1518_, v_x_1612_);
v___x_1621_ = l_Lean_IR_MapVars_mapFnBody(v_f_1518_, v_b_1616_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 2, v___x_1621_);
lean_ctor_set(v___x_1618_, 0, v___x_1620_);
v___x_1623_ = v___x_1618_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1620_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_n_1613_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v___x_1621_);
lean_ctor_set_uint8(v_reuseFailAlloc_1624_, sizeof(void*)*3, v_c_1614_);
lean_ctor_set_uint8(v_reuseFailAlloc_1624_, sizeof(void*)*3 + 1, v_persistent_1615_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
case 7:
{
lean_object* v_x_1626_; lean_object* v_n_1627_; uint8_t v_c_1628_; uint8_t v_persistent_1629_; lean_object* v_b_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1639_; 
v_x_1626_ = lean_ctor_get(v_x_1519_, 0);
v_n_1627_ = lean_ctor_get(v_x_1519_, 1);
v_c_1628_ = lean_ctor_get_uint8(v_x_1519_, sizeof(void*)*3);
v_persistent_1629_ = lean_ctor_get_uint8(v_x_1519_, sizeof(void*)*3 + 1);
v_b_1630_ = lean_ctor_get(v_x_1519_, 2);
v_isSharedCheck_1639_ = !lean_is_exclusive(v_x_1519_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1632_ = v_x_1519_;
v_isShared_1633_ = v_isSharedCheck_1639_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_b_1630_);
lean_inc(v_n_1627_);
lean_inc(v_x_1626_);
lean_dec(v_x_1519_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1639_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1637_; 
lean_inc_ref(v_f_1518_);
v___x_1634_ = lean_apply_1(v_f_1518_, v_x_1626_);
v___x_1635_ = l_Lean_IR_MapVars_mapFnBody(v_f_1518_, v_b_1630_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 2, v___x_1635_);
lean_ctor_set(v___x_1632_, 0, v___x_1634_);
v___x_1637_ = v___x_1632_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_n_1627_);
lean_ctor_set(v_reuseFailAlloc_1638_, 2, v___x_1635_);
lean_ctor_set_uint8(v_reuseFailAlloc_1638_, sizeof(void*)*3, v_c_1628_);
lean_ctor_set_uint8(v_reuseFailAlloc_1638_, sizeof(void*)*3 + 1, v_persistent_1629_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
case 8:
{
lean_object* v_x_1640_; lean_object* v_b_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1650_; 
v_x_1640_ = lean_ctor_get(v_x_1519_, 0);
v_b_1641_ = lean_ctor_get(v_x_1519_, 1);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_x_1519_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1643_ = v_x_1519_;
v_isShared_1644_ = v_isSharedCheck_1650_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_b_1641_);
lean_inc(v_x_1640_);
lean_dec(v_x_1519_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1650_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1648_; 
lean_inc_ref(v_f_1518_);
v___x_1645_ = lean_apply_1(v_f_1518_, v_x_1640_);
v___x_1646_ = l_Lean_IR_MapVars_mapFnBody(v_f_1518_, v_b_1641_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 1, v___x_1646_);
lean_ctor_set(v___x_1643_, 0, v___x_1645_);
v___x_1648_ = v___x_1643_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1645_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
case 9:
{
lean_object* v_tid_1651_; lean_object* v_x_1652_; lean_object* v_xType_1653_; lean_object* v_cs_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1665_; 
v_tid_1651_ = lean_ctor_get(v_x_1519_, 0);
v_x_1652_ = lean_ctor_get(v_x_1519_, 1);
v_xType_1653_ = lean_ctor_get(v_x_1519_, 2);
v_cs_1654_ = lean_ctor_get(v_x_1519_, 3);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_x_1519_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1656_ = v_x_1519_;
v_isShared_1657_ = v_isSharedCheck_1665_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_cs_1654_);
lean_inc(v_xType_1653_);
lean_inc(v_x_1652_);
lean_inc(v_tid_1651_);
lean_dec(v_x_1519_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1665_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; size_t v_sz_1659_; size_t v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1663_; 
lean_inc_ref(v_f_1518_);
v___x_1658_ = lean_apply_1(v_f_1518_, v_x_1652_);
v_sz_1659_ = lean_array_size(v_cs_1654_);
v___x_1660_ = ((size_t)0ULL);
v___x_1661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(v_f_1518_, v_sz_1659_, v___x_1660_, v_cs_1654_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 3, v___x_1661_);
lean_ctor_set(v___x_1656_, 1, v___x_1658_);
v___x_1663_ = v___x_1656_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_tid_1651_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v___x_1658_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_xType_1653_);
lean_ctor_set(v_reuseFailAlloc_1664_, 3, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
case 10:
{
lean_object* v_x_1666_; 
v_x_1666_ = lean_ctor_get(v_x_1519_, 0);
lean_inc(v_x_1666_);
if (lean_obj_tag(v_x_1666_) == 0)
{
lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1682_; 
v_isSharedCheck_1682_ = !lean_is_exclusive(v_x_1519_);
if (v_isSharedCheck_1682_ == 0)
{
lean_object* v_unused_1683_; 
v_unused_1683_ = lean_ctor_get(v_x_1519_, 0);
lean_dec(v_unused_1683_);
v___x_1668_ = v_x_1519_;
v_isShared_1669_ = v_isSharedCheck_1682_;
goto v_resetjp_1667_;
}
else
{
lean_dec(v_x_1519_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1682_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v_id_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1681_; 
v_id_1670_ = lean_ctor_get(v_x_1666_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_x_1666_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1672_ = v_x_1666_;
v_isShared_1673_ = v_isSharedCheck_1681_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_id_1670_);
lean_dec(v_x_1666_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1681_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1674_ = lean_apply_1(v_f_1518_, v_id_1670_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1674_);
v___x_1676_ = v___x_1672_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v___x_1678_; 
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v___x_1676_);
v___x_1678_ = v___x_1668_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_1518_);
return v_x_1519_;
}
}
case 11:
{
lean_object* v_j_1684_; lean_object* v_ys_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1693_; 
v_j_1684_ = lean_ctor_get(v_x_1519_, 0);
v_ys_1685_ = lean_ctor_get(v_x_1519_, 1);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_x_1519_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1687_ = v_x_1519_;
v_isShared_1688_ = v_isSharedCheck_1693_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_ys_1685_);
lean_inc(v_j_1684_);
lean_dec(v_x_1519_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1693_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1689_ = l_Lean_IR_MapVars_mapArgs(v_f_1518_, v_ys_1685_);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 1, v___x_1689_);
v___x_1691_ = v___x_1687_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_j_1684_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
default: 
{
lean_dec_ref(v_f_1518_);
return v_x_1519_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(lean_object* v_f_1694_, size_t v_sz_1695_, size_t v_i_1696_, lean_object* v_bs_1697_){
_start:
{
uint8_t v___x_1698_; 
v___x_1698_ = lean_usize_dec_lt(v_i_1696_, v_sz_1695_);
if (v___x_1698_ == 0)
{
lean_dec_ref(v_f_1694_);
return v_bs_1697_;
}
else
{
lean_object* v_v_1699_; lean_object* v___x_1700_; lean_object* v_bs_x27_1701_; lean_object* v___y_1703_; 
v_v_1699_ = lean_array_uget(v_bs_1697_, v_i_1696_);
v___x_1700_ = lean_unsigned_to_nat(0u);
v_bs_x27_1701_ = lean_array_uset(v_bs_1697_, v_i_1696_, v___x_1700_);
if (lean_obj_tag(v_v_1699_) == 0)
{
lean_object* v_info_1708_; lean_object* v_b_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1717_; 
v_info_1708_ = lean_ctor_get(v_v_1699_, 0);
v_b_1709_ = lean_ctor_get(v_v_1699_, 1);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_v_1699_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1711_ = v_v_1699_;
v_isShared_1712_ = v_isSharedCheck_1717_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_b_1709_);
lean_inc(v_info_1708_);
lean_dec(v_v_1699_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1717_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
lean_inc_ref(v_f_1694_);
v___x_1713_ = l_Lean_IR_MapVars_mapFnBody(v_f_1694_, v_b_1709_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 1, v___x_1713_);
v___x_1715_ = v___x_1711_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_info_1708_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
v___y_1703_ = v___x_1715_;
goto v___jp_1702_;
}
}
}
else
{
lean_object* v_b_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1726_; 
v_b_1718_ = lean_ctor_get(v_v_1699_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_v_1699_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1720_ = v_v_1699_;
v_isShared_1721_ = v_isSharedCheck_1726_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_b_1718_);
lean_dec(v_v_1699_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1726_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v___x_1724_; 
lean_inc_ref(v_f_1694_);
v___x_1722_ = l_Lean_IR_MapVars_mapFnBody(v_f_1694_, v_b_1718_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1722_);
v___x_1724_ = v___x_1720_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
v___y_1703_ = v___x_1724_;
goto v___jp_1702_;
}
}
}
v___jp_1702_:
{
size_t v___x_1704_; size_t v___x_1705_; lean_object* v___x_1706_; 
v___x_1704_ = ((size_t)1ULL);
v___x_1705_ = lean_usize_add(v_i_1696_, v___x_1704_);
v___x_1706_ = lean_array_uset(v_bs_x27_1701_, v_i_1696_, v___y_1703_);
v_i_1696_ = v___x_1705_;
v_bs_1697_ = v___x_1706_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0___boxed(lean_object* v_f_1727_, lean_object* v_sz_1728_, lean_object* v_i_1729_, lean_object* v_bs_1730_){
_start:
{
size_t v_sz_boxed_1731_; size_t v_i_boxed_1732_; lean_object* v_res_1733_; 
v_sz_boxed_1731_ = lean_unbox_usize(v_sz_1728_);
lean_dec(v_sz_1728_);
v_i_boxed_1732_ = lean_unbox_usize(v_i_1729_);
lean_dec(v_i_1729_);
v_res_1733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(v_f_1727_, v_sz_boxed_1731_, v_i_boxed_1732_, v_bs_1730_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_mapVars(lean_object* v_f_1734_, lean_object* v_b_1735_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Lean_IR_MapVars_mapFnBody(v_f_1734_, v_b_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lam__0(lean_object* v_x_1737_, lean_object* v_y_1738_, lean_object* v_z_1739_){
_start:
{
uint8_t v___x_1740_; 
v___x_1740_ = l_Lean_IR_instBEqVarId_beq(v_x_1737_, v_z_1739_);
if (v___x_1740_ == 0)
{
lean_inc(v_z_1739_);
return v_z_1739_;
}
else
{
lean_inc(v_y_1738_);
return v_y_1738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lam__0___boxed(lean_object* v_x_1741_, lean_object* v_y_1742_, lean_object* v_z_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_IR_FnBody_replaceVar___lam__0(v_x_1741_, v_y_1742_, v_z_1743_);
lean_dec(v_z_1743_);
lean_dec(v_y_1742_);
lean_dec(v_x_1741_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar(lean_object* v_x_1745_, lean_object* v_y_1746_, lean_object* v_b_1747_){
_start:
{
lean_object* v___f_1748_; lean_object* v___x_1749_; 
v___f_1748_ = lean_alloc_closure((void*)(l_Lean_IR_FnBody_replaceVar___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1748_, 0, v_x_1745_);
lean_closure_set(v___f_1748_, 1, v_y_1746_);
v___x_1749_ = l_Lean_IR_MapVars_mapFnBody(v___f_1748_, v_b_1747_);
return v___x_1749_;
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
