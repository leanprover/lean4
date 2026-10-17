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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody_default__1;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_IR_Alt_body(lean_object*);
uint8_t l_Lean_IR_FnBody_isVarDecl(lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* l_Lean_IR_FnBody_targetVar(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_IR_instBEqVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setTargetVar(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__0_value;
static const lean_closure_object l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__5 = (const lean_object*)&l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__6 = (const lean_object*)&l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0(lean_object*);
static const lean_string_object l_Lean_IR_NormalizeIds_normExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.IR.NormIds"};
static const lean_object* l_Lean_IR_NormalizeIds_normExpr___closed__0 = (const lean_object*)&l_Lean_IR_NormalizeIds_normExpr___closed__0_value;
static const lean_string_object l_Lean_IR_NormalizeIds_normExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.IR.NormalizeIds.normExpr"};
static const lean_object* l_Lean_IR_NormalizeIds_normExpr___closed__1 = (const lean_object*)&l_Lean_IR_NormalizeIds_normExpr___closed__1_value;
static const lean_string_object l_Lean_IR_NormalizeIds_normExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_IR_NormalizeIds_normExpr___closed__2 = (const lean_object*)&l_Lean_IR_NormalizeIds_normExpr___closed__2_value;
static lean_once_cell_t l_Lean_IR_NormalizeIds_normExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_NormalizeIds_normExpr___closed__3;
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
static const lean_closure_object l_Lean_IR_NormalizeIds_withParams___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_NormalizeIds_withParams___redArg___lam__2, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_IR_NormalizeIds_withVar___redArg___closed__0_value)} };
static const lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___closed__0 = (const lean_object*)&l_Lean_IR_NormalizeIds_withParams___redArg___closed__0_value;
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
case 19:
{
lean_object* v_j_404_; lean_object* v_xs_405_; lean_object* v_b_406_; lean_object* v___x_407_; lean_object* v_fst_408_; uint8_t v___x_409_; 
v_j_404_ = lean_ctor_get(v_x_397_, 0);
lean_inc(v_j_404_);
v_xs_405_ = lean_ctor_get(v_x_397_, 1);
lean_inc_ref(v_xs_405_);
v_b_406_ = lean_ctor_get(v_x_397_, 3);
lean_inc(v_b_406_);
lean_dec_ref_known(v_x_397_, 4);
v___x_407_ = l_Lean_IR_UniqueIds_checkId(v_j_404_, v_a_398_);
v_fst_408_ = lean_ctor_get(v___x_407_, 0);
v___x_409_ = lean_unbox(v_fst_408_);
if (v___x_409_ == 0)
{
lean_dec(v_b_406_);
lean_dec_ref(v_xs_405_);
return v___x_407_;
}
else
{
lean_object* v_snd_410_; lean_object* v___x_411_; lean_object* v_fst_412_; uint8_t v___x_413_; 
v_snd_410_ = lean_ctor_get(v___x_407_, 1);
lean_inc(v_snd_410_);
lean_dec_ref(v___x_407_);
v___x_411_ = l_Lean_IR_UniqueIds_checkParams(v_xs_405_, v_snd_410_);
lean_dec_ref(v_xs_405_);
v_fst_412_ = lean_ctor_get(v___x_411_, 0);
v___x_413_ = lean_unbox(v_fst_412_);
if (v___x_413_ == 0)
{
lean_dec(v_b_406_);
return v___x_411_;
}
else
{
lean_object* v_snd_414_; 
v_snd_414_ = lean_ctor_get(v___x_411_, 1);
lean_inc(v_snd_414_);
lean_dec_ref(v___x_411_);
v_x_397_ = v_b_406_;
v_a_398_ = v_snd_414_;
goto _start;
}
}
}
case 27:
{
lean_object* v_cs_416_; lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_cs_416_ = lean_ctor_get(v_x_397_, 3);
lean_inc_ref(v_cs_416_);
lean_dec_ref_known(v_x_397_, 4);
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = lean_array_get_size(v_cs_416_);
v___x_419_ = lean_nat_dec_lt(v___x_417_, v___x_418_);
if (v___x_419_ == 0)
{
lean_dec_ref(v_cs_416_);
v___y_400_ = v_a_398_;
goto v___jp_399_;
}
else
{
if (v___x_419_ == 0)
{
lean_dec_ref(v_cs_416_);
v___y_400_ = v_a_398_;
goto v___jp_399_;
}
else
{
size_t v___x_420_; size_t v___x_421_; lean_object* v___x_422_; lean_object* v_fst_423_; uint8_t v___x_424_; 
v___x_420_ = ((size_t)0ULL);
v___x_421_ = lean_usize_of_nat(v___x_418_);
v___x_422_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(v_cs_416_, v___x_420_, v___x_421_, v_a_398_);
lean_dec_ref(v_cs_416_);
v_fst_423_ = lean_ctor_get(v___x_422_, 0);
v___x_424_ = lean_unbox(v_fst_423_);
if (v___x_424_ == 0)
{
lean_object* v_snd_425_; 
v_snd_425_ = lean_ctor_get(v___x_422_, 1);
lean_inc(v_snd_425_);
lean_dec_ref(v___x_422_);
v___y_400_ = v_snd_425_;
goto v___jp_399_;
}
else
{
lean_object* v_snd_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_435_; 
v_snd_426_ = lean_ctor_get(v___x_422_, 1);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_435_ == 0)
{
lean_object* v_unused_436_; 
v_unused_436_ = lean_ctor_get(v___x_422_, 0);
lean_dec(v_unused_436_);
v___x_428_ = v___x_422_;
v_isShared_429_ = v_isSharedCheck_435_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_snd_426_);
lean_dec(v___x_422_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_435_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
uint8_t v___x_430_; lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_430_ = 0;
v___x_431_ = lean_box(v___x_430_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_431_);
v___x_433_ = v___x_428_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_snd_426_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
}
default: 
{
uint8_t v___x_437_; 
v___x_437_ = l_Lean_IR_FnBody_isVarDecl(v_x_397_);
if (v___x_437_ == 0)
{
uint8_t v___x_438_; 
v___x_438_ = l_Lean_IR_FnBody_isTerminal(v_x_397_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_IR_FnBody_body(v_x_397_);
lean_dec(v_x_397_);
v_x_397_ = v___x_439_;
goto _start;
}
else
{
lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec(v_x_397_);
v___x_441_ = lean_box(v___x_438_);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v_a_398_);
return v___x_442_;
}
}
else
{
lean_object* v_x_443_; lean_object* v___x_444_; lean_object* v_fst_445_; uint8_t v___x_446_; 
v_x_443_ = l_Lean_IR_FnBody_targetVar(v_x_397_);
v___x_444_ = l_Lean_IR_UniqueIds_checkId(v_x_443_, v_a_398_);
v_fst_445_ = lean_ctor_get(v___x_444_, 0);
v___x_446_ = lean_unbox(v_fst_445_);
if (v___x_446_ == 0)
{
lean_dec(v_x_397_);
return v___x_444_;
}
else
{
lean_object* v_snd_447_; lean_object* v_b_448_; 
v_snd_447_ = lean_ctor_get(v___x_444_, 1);
lean_inc(v_snd_447_);
lean_dec_ref(v___x_444_);
v_b_448_ = l_Lean_IR_FnBody_body(v_x_397_);
lean_dec(v_x_397_);
v_x_397_ = v_b_448_;
v_a_398_ = v_snd_447_;
goto _start;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(lean_object* v_as_450_, size_t v_i_451_, size_t v_stop_452_, lean_object* v___y_453_){
_start:
{
uint8_t v___x_454_; 
v___x_454_ = lean_usize_dec_eq(v_i_451_, v_stop_452_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v_fst_458_; uint8_t v___x_459_; 
v___x_455_ = lean_array_uget_borrowed(v_as_450_, v_i_451_);
v___x_456_ = l_Lean_IR_Alt_body(v___x_455_);
v___x_457_ = l_Lean_IR_UniqueIds_checkFnBody(v___x_456_, v___y_453_);
v_fst_458_ = lean_ctor_get(v___x_457_, 0);
v___x_459_ = lean_unbox(v_fst_458_);
if (v___x_459_ == 0)
{
lean_object* v_snd_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_469_; 
v_snd_460_ = lean_ctor_get(v___x_457_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; 
v_unused_470_ = lean_ctor_get(v___x_457_, 0);
lean_dec(v_unused_470_);
v___x_462_ = v___x_457_;
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_snd_460_);
lean_dec(v___x_457_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
uint8_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_464_ = 1;
v___x_465_ = lean_box(v___x_464_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_465_);
v___x_467_ = v___x_462_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_snd_460_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
else
{
lean_object* v_snd_471_; size_t v___x_472_; size_t v___x_473_; 
v_snd_471_ = lean_ctor_get(v___x_457_, 1);
lean_inc(v_snd_471_);
lean_dec_ref(v___x_457_);
v___x_472_ = ((size_t)1ULL);
v___x_473_ = lean_usize_add(v_i_451_, v___x_472_);
v_i_451_ = v___x_473_;
v___y_453_ = v_snd_471_;
goto _start;
}
}
else
{
uint8_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = 0;
v___x_476_ = lean_box(v___x_475_);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___y_453_);
return v___x_477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0___boxed(lean_object* v_as_478_, lean_object* v_i_479_, lean_object* v_stop_480_, lean_object* v___y_481_){
_start:
{
size_t v_i_boxed_482_; size_t v_stop_boxed_483_; lean_object* v_res_484_; 
v_i_boxed_482_ = lean_unbox_usize(v_i_479_);
lean_dec(v_i_479_);
v_stop_boxed_483_ = lean_unbox_usize(v_stop_480_);
lean_dec(v_stop_480_);
v_res_484_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(v_as_478_, v_i_boxed_482_, v_stop_boxed_483_, v___y_481_);
lean_dec_ref(v_as_478_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkDecl(lean_object* v_x_485_, lean_object* v_a_486_){
_start:
{
if (lean_obj_tag(v_x_485_) == 0)
{
lean_object* v_xs_487_; lean_object* v_body_488_; lean_object* v___x_489_; lean_object* v_fst_490_; uint8_t v___x_491_; 
v_xs_487_ = lean_ctor_get(v_x_485_, 1);
lean_inc_ref(v_xs_487_);
v_body_488_ = lean_ctor_get(v_x_485_, 3);
lean_inc(v_body_488_);
lean_dec_ref_known(v_x_485_, 5);
v___x_489_ = l_Lean_IR_UniqueIds_checkParams(v_xs_487_, v_a_486_);
lean_dec_ref(v_xs_487_);
v_fst_490_ = lean_ctor_get(v___x_489_, 0);
v___x_491_ = lean_unbox(v_fst_490_);
if (v___x_491_ == 0)
{
lean_dec(v_body_488_);
return v___x_489_;
}
else
{
lean_object* v_snd_492_; lean_object* v___x_493_; 
v_snd_492_ = lean_ctor_get(v___x_489_, 1);
lean_inc(v_snd_492_);
lean_dec_ref(v___x_489_);
v___x_493_ = l_Lean_IR_UniqueIds_checkFnBody(v_body_488_, v_snd_492_);
return v___x_493_;
}
}
else
{
lean_object* v_xs_494_; lean_object* v___x_495_; 
v_xs_494_ = lean_ctor_get(v_x_485_, 1);
lean_inc_ref(v_xs_494_);
lean_dec_ref_known(v_x_485_, 4);
v___x_495_ = l_Lean_IR_UniqueIds_checkParams(v_xs_494_, v_a_486_);
lean_dec_ref(v_xs_494_);
return v___x_495_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Decl_uniqueIds(lean_object* v_d_496_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v_fst_499_; uint8_t v___x_500_; 
v___x_497_ = lean_box(1);
v___x_498_ = l_Lean_IR_UniqueIds_checkDecl(v_d_496_, v___x_497_);
v_fst_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_fst_499_);
lean_dec_ref(v___x_498_);
v___x_500_ = lean_unbox(v_fst_499_);
lean_dec(v_fst_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_uniqueIds___boxed(lean_object* v_d_501_){
_start:
{
uint8_t v_res_502_; lean_object* v_r_503_; 
v_res_502_ = l_Lean_IR_Decl_uniqueIds(v_d_501_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(lean_object* v_t_504_, lean_object* v_k_505_){
_start:
{
if (lean_obj_tag(v_t_504_) == 0)
{
lean_object* v_k_506_; lean_object* v_v_507_; lean_object* v_l_508_; lean_object* v_r_509_; uint8_t v___x_510_; 
v_k_506_ = lean_ctor_get(v_t_504_, 1);
v_v_507_ = lean_ctor_get(v_t_504_, 2);
v_l_508_ = lean_ctor_get(v_t_504_, 3);
v_r_509_ = lean_ctor_get(v_t_504_, 4);
v___x_510_ = lean_nat_dec_lt(v_k_505_, v_k_506_);
if (v___x_510_ == 0)
{
uint8_t v___x_511_; 
v___x_511_ = lean_nat_dec_eq(v_k_505_, v_k_506_);
if (v___x_511_ == 0)
{
v_t_504_ = v_r_509_;
goto _start;
}
else
{
lean_object* v___x_513_; 
lean_inc(v_v_507_);
v___x_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_513_, 0, v_v_507_);
return v___x_513_;
}
}
else
{
v_t_504_ = v_l_508_;
goto _start;
}
}
else
{
lean_object* v___x_515_; 
v___x_515_ = lean_box(0);
return v___x_515_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg___boxed(lean_object* v_t_516_, lean_object* v_k_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_t_516_, v_k_517_);
lean_dec(v_k_517_);
lean_dec(v_t_516_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normIndex(lean_object* v_x_519_, lean_object* v_m_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_m_520_, v_x_519_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_inc(v_x_519_);
return v_x_519_;
}
else
{
lean_object* v_val_522_; 
v_val_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_val_522_);
lean_dec_ref_known(v___x_521_, 1);
return v_val_522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normIndex___boxed(lean_object* v_x_523_, lean_object* v_m_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_IR_NormalizeIds_normIndex(v_x_523_, v_m_524_);
lean_dec(v_m_524_);
lean_dec(v_x_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0(lean_object* v_00_u03b4_526_, lean_object* v_t_527_, lean_object* v_k_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_t_527_, v_k_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___boxed(lean_object* v_00_u03b4_530_, lean_object* v_t_531_, lean_object* v_k_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0(v_00_u03b4_530_, v_t_531_, v_k_532_);
lean_dec(v_k_532_);
lean_dec(v_t_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normVar(lean_object* v_x_534_, lean_object* v_a_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_IR_NormalizeIds_normIndex(v_x_534_, v_a_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normVar___boxed(lean_object* v_x_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_IR_NormalizeIds_normVar(v_x_537_, v_a_538_);
lean_dec(v_a_538_);
lean_dec(v_x_537_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normJP(lean_object* v_x_540_, lean_object* v_a_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_IR_NormalizeIds_normIndex(v_x_540_, v_a_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normJP___boxed(lean_object* v_x_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_IR_NormalizeIds_normJP(v_x_543_, v_a_544_);
lean_dec(v_a_544_);
lean_dec(v_x_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArg(lean_object* v_x_546_, lean_object* v_a_547_){
_start:
{
if (lean_obj_tag(v_x_546_) == 0)
{
lean_object* v_id_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_556_; 
v_id_548_ = lean_ctor_get(v_x_546_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v_x_546_);
if (v_isSharedCheck_556_ == 0)
{
v___x_550_ = v_x_546_;
v_isShared_551_ = v_isSharedCheck_556_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_id_548_);
lean_dec(v_x_546_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_556_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = l_Lean_IR_NormalizeIds_normIndex(v_id_548_, v_a_547_);
lean_dec(v_id_548_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_552_);
v___x_554_ = v___x_550_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
else
{
return v_x_546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArg___boxed(lean_object* v_x_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_IR_NormalizeIds_normArg(v_x_557_, v_a_558_);
lean_dec(v_a_558_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(lean_object* v_m_560_, size_t v_sz_561_, size_t v_i_562_, lean_object* v_bs_563_){
_start:
{
uint8_t v___x_564_; 
v___x_564_ = lean_usize_dec_lt(v_i_562_, v_sz_561_);
if (v___x_564_ == 0)
{
return v_bs_563_;
}
else
{
lean_object* v_v_565_; lean_object* v___x_566_; lean_object* v_bs_x27_567_; lean_object* v___x_568_; size_t v___x_569_; size_t v___x_570_; lean_object* v___x_571_; 
v_v_565_ = lean_array_uget(v_bs_563_, v_i_562_);
v___x_566_ = lean_unsigned_to_nat(0u);
v_bs_x27_567_ = lean_array_uset(v_bs_563_, v_i_562_, v___x_566_);
v___x_568_ = l_Lean_IR_NormalizeIds_normArg(v_v_565_, v_m_560_);
v___x_569_ = ((size_t)1ULL);
v___x_570_ = lean_usize_add(v_i_562_, v___x_569_);
v___x_571_ = lean_array_uset(v_bs_x27_567_, v_i_562_, v___x_568_);
v_i_562_ = v___x_570_;
v_bs_563_ = v___x_571_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0___boxed(lean_object* v_m_573_, lean_object* v_sz_574_, lean_object* v_i_575_, lean_object* v_bs_576_){
_start:
{
size_t v_sz_boxed_577_; size_t v_i_boxed_578_; lean_object* v_res_579_; 
v_sz_boxed_577_ = lean_unbox_usize(v_sz_574_);
lean_dec(v_sz_574_);
v_i_boxed_578_ = lean_unbox_usize(v_i_575_);
lean_dec(v_i_575_);
v_res_579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(v_m_573_, v_sz_boxed_577_, v_i_boxed_578_, v_bs_576_);
lean_dec(v_m_573_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArgs(lean_object* v_as_580_, lean_object* v_m_581_){
_start:
{
size_t v_sz_582_; size_t v___x_583_; lean_object* v___x_584_; 
v_sz_582_ = lean_array_size(v_as_580_);
v___x_583_ = ((size_t)0ULL);
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(v_m_581_, v_sz_582_, v___x_583_, v_as_580_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArgs___boxed(lean_object* v_as_585_, lean_object* v_m_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_IR_NormalizeIds_normArgs(v_as_585_, v_m_586_);
lean_dec(v_m_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0(lean_object* v_msg_595_){
_start:
{
lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___f_600_; lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___f_596_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__0));
v___f_597_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__1));
v___f_598_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__2));
v___f_599_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__3));
v___f_600_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__4));
v___f_601_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__5));
v___f_602_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__6));
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v___f_596_);
lean_ctor_set(v___x_603_, 1, v___f_597_);
v___x_604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v___f_598_);
lean_ctor_set(v___x_604_, 2, v___f_599_);
lean_ctor_set(v___x_604_, 3, v___f_600_);
lean_ctor_set(v___x_604_, 4, v___f_601_);
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___f_602_);
v___x_606_ = l_Lean_IR_instInhabitedFnBody_default__1;
v___x_607_ = l_instInhabitedOfMonad___redArg(v___x_605_, v___x_606_);
v___x_608_ = lean_panic_fn_borrowed(v___x_607_, v_msg_595_);
lean_dec(v___x_607_);
return v___x_608_;
}
}
static lean_object* _init_l_Lean_IR_NormalizeIds_normExpr___closed__3(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_612_ = ((lean_object*)(l_Lean_IR_NormalizeIds_normExpr___closed__2));
v___x_613_ = lean_unsigned_to_nat(12u);
v___x_614_ = lean_unsigned_to_nat(87u);
v___x_615_ = ((lean_object*)(l_Lean_IR_NormalizeIds_normExpr___closed__1));
v___x_616_ = ((lean_object*)(l_Lean_IR_NormalizeIds_normExpr___closed__0));
v___x_617_ = l_mkPanicMessageWithDecl(v___x_616_, v___x_615_, v___x_614_, v___x_613_, v___x_612_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normExpr(lean_object* v_x_618_, lean_object* v_x_619_){
_start:
{
switch(lean_obj_tag(v_x_618_))
{
case 0:
{
lean_object* v_tgt_620_; lean_object* v_b_621_; lean_object* v_i_622_; lean_object* v_ys_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_631_; 
v_tgt_620_ = lean_ctor_get(v_x_618_, 0);
v_b_621_ = lean_ctor_get(v_x_618_, 1);
v_i_622_ = lean_ctor_get(v_x_618_, 2);
v_ys_623_ = lean_ctor_get(v_x_618_, 3);
v_isSharedCheck_631_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_631_ == 0)
{
v___x_625_ = v_x_618_;
v_isShared_626_ = v_isSharedCheck_631_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_ys_623_);
lean_inc(v_i_622_);
lean_inc(v_b_621_);
lean_inc(v_tgt_620_);
lean_dec(v_x_618_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_631_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_627_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_623_, v_x_619_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 3, v___x_627_);
v___x_629_ = v___x_625_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_tgt_620_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_b_621_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v_i_622_);
lean_ctor_set(v_reuseFailAlloc_630_, 3, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
case 1:
{
lean_object* v_tgt_632_; lean_object* v_b_633_; lean_object* v_n_634_; lean_object* v_x_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_643_; 
v_tgt_632_ = lean_ctor_get(v_x_618_, 0);
v_b_633_ = lean_ctor_get(v_x_618_, 1);
v_n_634_ = lean_ctor_get(v_x_618_, 2);
v_x_635_ = lean_ctor_get(v_x_618_, 3);
v_isSharedCheck_643_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_643_ == 0)
{
v___x_637_ = v_x_618_;
v_isShared_638_ = v_isSharedCheck_643_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_x_635_);
lean_inc(v_n_634_);
lean_inc(v_b_633_);
lean_inc(v_tgt_632_);
lean_dec(v_x_618_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_643_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_639_ = l_Lean_IR_NormalizeIds_normIndex(v_x_635_, v_x_619_);
lean_dec(v_x_635_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 3, v___x_639_);
v___x_641_ = v___x_637_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_tgt_632_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_b_633_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v_n_634_);
lean_ctor_set(v_reuseFailAlloc_642_, 3, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
case 2:
{
lean_object* v_tgt_644_; lean_object* v_b_645_; lean_object* v_x_646_; lean_object* v_i_647_; uint8_t v_updtHeader_648_; lean_object* v_ys_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_658_; 
v_tgt_644_ = lean_ctor_get(v_x_618_, 0);
v_b_645_ = lean_ctor_get(v_x_618_, 1);
v_x_646_ = lean_ctor_get(v_x_618_, 2);
v_i_647_ = lean_ctor_get(v_x_618_, 3);
v_updtHeader_648_ = lean_ctor_get_uint8(v_x_618_, sizeof(void*)*5);
v_ys_649_ = lean_ctor_get(v_x_618_, 4);
v_isSharedCheck_658_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_658_ == 0)
{
v___x_651_ = v_x_618_;
v_isShared_652_ = v_isSharedCheck_658_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_ys_649_);
lean_inc(v_i_647_);
lean_inc(v_x_646_);
lean_inc(v_b_645_);
lean_inc(v_tgt_644_);
lean_dec(v_x_618_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_658_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_653_ = l_Lean_IR_NormalizeIds_normIndex(v_x_646_, v_x_619_);
lean_dec(v_x_646_);
v___x_654_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_649_, v_x_619_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 4, v___x_654_);
lean_ctor_set(v___x_651_, 2, v___x_653_);
v___x_656_ = v___x_651_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(2, 5, 1);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_tgt_644_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_b_645_);
lean_ctor_set(v_reuseFailAlloc_657_, 2, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_657_, 3, v_i_647_);
lean_ctor_set(v_reuseFailAlloc_657_, 4, v___x_654_);
lean_ctor_set_uint8(v_reuseFailAlloc_657_, sizeof(void*)*5, v_updtHeader_648_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
case 3:
{
lean_object* v_tgt_659_; lean_object* v_b_660_; lean_object* v_i_661_; lean_object* v_x_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_670_; 
v_tgt_659_ = lean_ctor_get(v_x_618_, 0);
v_b_660_ = lean_ctor_get(v_x_618_, 1);
v_i_661_ = lean_ctor_get(v_x_618_, 2);
v_x_662_ = lean_ctor_get(v_x_618_, 3);
v_isSharedCheck_670_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_670_ == 0)
{
v___x_664_ = v_x_618_;
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_x_662_);
lean_inc(v_i_661_);
lean_inc(v_b_660_);
lean_inc(v_tgt_659_);
lean_dec(v_x_618_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_666_ = l_Lean_IR_NormalizeIds_normIndex(v_x_662_, v_x_619_);
lean_dec(v_x_662_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 3, v___x_666_);
v___x_668_ = v___x_664_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_tgt_659_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_b_660_);
lean_ctor_set(v_reuseFailAlloc_669_, 2, v_i_661_);
lean_ctor_set(v_reuseFailAlloc_669_, 3, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
case 4:
{
lean_object* v_tgt_671_; lean_object* v_b_672_; lean_object* v_i_673_; lean_object* v_x_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_682_; 
v_tgt_671_ = lean_ctor_get(v_x_618_, 0);
v_b_672_ = lean_ctor_get(v_x_618_, 1);
v_i_673_ = lean_ctor_get(v_x_618_, 2);
v_x_674_ = lean_ctor_get(v_x_618_, 3);
v_isSharedCheck_682_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_682_ == 0)
{
v___x_676_ = v_x_618_;
v_isShared_677_ = v_isSharedCheck_682_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_x_674_);
lean_inc(v_i_673_);
lean_inc(v_b_672_);
lean_inc(v_tgt_671_);
lean_dec(v_x_618_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_682_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = l_Lean_IR_NormalizeIds_normIndex(v_x_674_, v_x_619_);
lean_dec(v_x_674_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 3, v___x_678_);
v___x_680_ = v___x_676_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_tgt_671_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_b_672_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_i_673_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
case 5:
{
lean_object* v_tgt_683_; lean_object* v_b_684_; lean_object* v_ty_685_; lean_object* v_n_686_; lean_object* v_offset_687_; lean_object* v_x_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_696_; 
v_tgt_683_ = lean_ctor_get(v_x_618_, 0);
v_b_684_ = lean_ctor_get(v_x_618_, 1);
v_ty_685_ = lean_ctor_get(v_x_618_, 2);
v_n_686_ = lean_ctor_get(v_x_618_, 3);
v_offset_687_ = lean_ctor_get(v_x_618_, 4);
v_x_688_ = lean_ctor_get(v_x_618_, 5);
v_isSharedCheck_696_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_696_ == 0)
{
v___x_690_ = v_x_618_;
v_isShared_691_ = v_isSharedCheck_696_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_x_688_);
lean_inc(v_offset_687_);
lean_inc(v_n_686_);
lean_inc(v_ty_685_);
lean_inc(v_b_684_);
lean_inc(v_tgt_683_);
lean_dec(v_x_618_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_696_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_692_ = l_Lean_IR_NormalizeIds_normIndex(v_x_688_, v_x_619_);
lean_dec(v_x_688_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 5, v___x_692_);
v___x_694_ = v___x_690_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_tgt_683_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_b_684_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_ty_685_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_n_686_);
lean_ctor_set(v_reuseFailAlloc_695_, 4, v_offset_687_);
lean_ctor_set(v_reuseFailAlloc_695_, 5, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
case 6:
{
lean_object* v_tgt_697_; lean_object* v_b_698_; lean_object* v_ty_699_; lean_object* v_c_700_; lean_object* v_ys_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_709_; 
v_tgt_697_ = lean_ctor_get(v_x_618_, 0);
v_b_698_ = lean_ctor_get(v_x_618_, 1);
v_ty_699_ = lean_ctor_get(v_x_618_, 2);
v_c_700_ = lean_ctor_get(v_x_618_, 3);
v_ys_701_ = lean_ctor_get(v_x_618_, 4);
v_isSharedCheck_709_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_709_ == 0)
{
v___x_703_ = v_x_618_;
v_isShared_704_ = v_isSharedCheck_709_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_ys_701_);
lean_inc(v_c_700_);
lean_inc(v_ty_699_);
lean_inc(v_b_698_);
lean_inc(v_tgt_697_);
lean_dec(v_x_618_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_709_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_705_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_701_, v_x_619_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v___x_705_);
v___x_707_ = v___x_703_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(6, 5, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_tgt_697_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_b_698_);
lean_ctor_set(v_reuseFailAlloc_708_, 2, v_ty_699_);
lean_ctor_set(v_reuseFailAlloc_708_, 3, v_c_700_);
lean_ctor_set(v_reuseFailAlloc_708_, 4, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
case 7:
{
lean_object* v_tgt_710_; lean_object* v_b_711_; lean_object* v_c_712_; lean_object* v_ys_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_721_; 
v_tgt_710_ = lean_ctor_get(v_x_618_, 0);
v_b_711_ = lean_ctor_get(v_x_618_, 1);
v_c_712_ = lean_ctor_get(v_x_618_, 2);
v_ys_713_ = lean_ctor_get(v_x_618_, 3);
v_isSharedCheck_721_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_721_ == 0)
{
v___x_715_ = v_x_618_;
v_isShared_716_ = v_isSharedCheck_721_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_ys_713_);
lean_inc(v_c_712_);
lean_inc(v_b_711_);
lean_inc(v_tgt_710_);
lean_dec(v_x_618_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_721_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_713_, v_x_619_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 3, v___x_717_);
v___x_719_ = v___x_715_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_tgt_710_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_b_711_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v_c_712_);
lean_ctor_set(v_reuseFailAlloc_720_, 3, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
case 8:
{
lean_object* v_tgt_722_; lean_object* v_b_723_; lean_object* v_x_724_; lean_object* v_ys_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_734_; 
v_tgt_722_ = lean_ctor_get(v_x_618_, 0);
v_b_723_ = lean_ctor_get(v_x_618_, 1);
v_x_724_ = lean_ctor_get(v_x_618_, 2);
v_ys_725_ = lean_ctor_get(v_x_618_, 3);
v_isSharedCheck_734_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_734_ == 0)
{
v___x_727_ = v_x_618_;
v_isShared_728_ = v_isSharedCheck_734_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_ys_725_);
lean_inc(v_x_724_);
lean_inc(v_b_723_);
lean_inc(v_tgt_722_);
lean_dec(v_x_618_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_734_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_729_ = l_Lean_IR_NormalizeIds_normIndex(v_x_724_, v_x_619_);
lean_dec(v_x_724_);
v___x_730_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_725_, v_x_619_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 3, v___x_730_);
lean_ctor_set(v___x_727_, 2, v___x_729_);
v___x_732_ = v___x_727_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_tgt_722_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_b_723_);
lean_ctor_set(v_reuseFailAlloc_733_, 2, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_733_, 3, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
case 9:
{
lean_object* v_tgt_735_; lean_object* v_b_736_; lean_object* v_ty_737_; lean_object* v_x_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_746_; 
v_tgt_735_ = lean_ctor_get(v_x_618_, 0);
v_b_736_ = lean_ctor_get(v_x_618_, 1);
v_ty_737_ = lean_ctor_get(v_x_618_, 2);
v_x_738_ = lean_ctor_get(v_x_618_, 3);
v_isSharedCheck_746_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_746_ == 0)
{
v___x_740_ = v_x_618_;
v_isShared_741_ = v_isSharedCheck_746_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_x_738_);
lean_inc(v_ty_737_);
lean_inc(v_b_736_);
lean_inc(v_tgt_735_);
lean_dec(v_x_618_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_746_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_742_ = l_Lean_IR_NormalizeIds_normIndex(v_x_738_, v_x_619_);
lean_dec(v_x_738_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 3, v___x_742_);
v___x_744_ = v___x_740_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_tgt_735_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_b_736_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v_ty_737_);
lean_ctor_set(v_reuseFailAlloc_745_, 3, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
case 10:
{
lean_object* v_tgt_747_; lean_object* v_b_748_; lean_object* v_ty_749_; lean_object* v_x_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_758_; 
v_tgt_747_ = lean_ctor_get(v_x_618_, 0);
v_b_748_ = lean_ctor_get(v_x_618_, 1);
v_ty_749_ = lean_ctor_get(v_x_618_, 2);
v_x_750_ = lean_ctor_get(v_x_618_, 3);
v_isSharedCheck_758_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_758_ == 0)
{
v___x_752_ = v_x_618_;
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_x_750_);
lean_inc(v_ty_749_);
lean_inc(v_b_748_);
lean_inc(v_tgt_747_);
lean_dec(v_x_618_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_754_ = l_Lean_IR_NormalizeIds_normIndex(v_x_750_, v_x_619_);
lean_dec(v_x_750_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 3, v___x_754_);
v___x_756_ = v___x_752_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_tgt_747_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_b_748_);
lean_ctor_set(v_reuseFailAlloc_757_, 2, v_ty_749_);
lean_ctor_set(v_reuseFailAlloc_757_, 3, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
case 18:
{
lean_object* v_tgt_759_; lean_object* v_b_760_; lean_object* v_x_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_769_; 
v_tgt_759_ = lean_ctor_get(v_x_618_, 0);
v_b_760_ = lean_ctor_get(v_x_618_, 1);
v_x_761_ = lean_ctor_get(v_x_618_, 2);
v_isSharedCheck_769_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_769_ == 0)
{
v___x_763_ = v_x_618_;
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_x_761_);
lean_inc(v_b_760_);
lean_inc(v_tgt_759_);
lean_dec(v_x_618_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_765_ = l_Lean_IR_NormalizeIds_normIndex(v_x_761_, v_x_619_);
lean_dec(v_x_761_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 2, v___x_765_);
v___x_767_ = v___x_763_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(18, 3, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_tgt_759_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_b_760_);
lean_ctor_set(v_reuseFailAlloc_768_, 2, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
case 11:
{
return v_x_618_;
}
case 12:
{
return v_x_618_;
}
case 13:
{
return v_x_618_;
}
case 14:
{
return v_x_618_;
}
case 15:
{
return v_x_618_;
}
case 16:
{
return v_x_618_;
}
case 17:
{
return v_x_618_;
}
default: 
{
lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec(v_x_618_);
v___x_770_ = lean_obj_once(&l_Lean_IR_NormalizeIds_normExpr___closed__3, &l_Lean_IR_NormalizeIds_normExpr___closed__3_once, _init_l_Lean_IR_NormalizeIds_normExpr___closed__3);
v___x_771_ = l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0(v___x_770_);
return v___x_771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normExpr___boxed(lean_object* v_x_772_, lean_object* v_x_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_IR_NormalizeIds_normExpr(v_x_772_, v_x_773_);
lean_dec(v_x_773_);
return v_res_774_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_NormalizeIds_withVar___redArg___lam__0(lean_object* v_x_775_, lean_object* v_y_776_){
_start:
{
uint8_t v___x_777_; 
v___x_777_ = lean_nat_dec_lt(v_x_775_, v_y_776_);
if (v___x_777_ == 0)
{
uint8_t v___x_778_; 
v___x_778_ = lean_nat_dec_eq(v_x_775_, v_y_776_);
if (v___x_778_ == 0)
{
uint8_t v___x_779_; 
v___x_779_ = 2;
return v___x_779_;
}
else
{
uint8_t v___x_780_; 
v___x_780_ = 1;
return v___x_780_;
}
}
else
{
uint8_t v___x_781_; 
v___x_781_ = 0;
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg___lam__0___boxed(lean_object* v_x_782_, lean_object* v_y_783_){
_start:
{
uint8_t v_res_784_; lean_object* v_r_785_; 
v_res_784_ = l_Lean_IR_NormalizeIds_withVar___redArg___lam__0(v_x_782_, v_y_783_);
lean_dec(v_y_783_);
lean_dec(v_x_782_);
v_r_785_ = lean_box(v_res_784_);
return v_r_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg(lean_object* v_x_787_, lean_object* v_k_788_, lean_object* v_m_789_, lean_object* v_a_790_){
_start:
{
lean_object* v___f_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___f_791_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_792_ = lean_unsigned_to_nat(1u);
v___x_793_ = lean_nat_add(v_a_790_, v___x_792_);
lean_inc(v_m_789_);
lean_inc(v_a_790_);
v___x_794_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_791_, v_x_787_, v_a_790_, v_m_789_);
v___x_795_ = lean_apply_3(v_k_788_, v_a_790_, v___x_794_, v___x_793_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg___boxed(lean_object* v_x_796_, lean_object* v_k_797_, lean_object* v_m_798_, lean_object* v_a_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_IR_NormalizeIds_withVar___redArg(v_x_796_, v_k_797_, v_m_798_, v_a_799_);
lean_dec(v_m_798_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar(lean_object* v_00_u03b1_801_, lean_object* v_x_802_, lean_object* v_k_803_, lean_object* v_m_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___f_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___f_806_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_807_ = lean_unsigned_to_nat(1u);
v___x_808_ = lean_nat_add(v_a_805_, v___x_807_);
lean_inc(v_m_804_);
lean_inc(v_a_805_);
v___x_809_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_806_, v_x_802_, v_a_805_, v_m_804_);
v___x_810_ = lean_apply_3(v_k_803_, v_a_805_, v___x_809_, v___x_808_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___boxed(lean_object* v_00_u03b1_811_, lean_object* v_x_812_, lean_object* v_k_813_, lean_object* v_m_814_, lean_object* v_a_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_IR_NormalizeIds_withVar(v_00_u03b1_811_, v_x_812_, v_k_813_, v_m_814_, v_a_815_);
lean_dec(v_m_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___redArg(lean_object* v_x_817_, lean_object* v_k_818_, lean_object* v_m_819_, lean_object* v_a_820_){
_start:
{
lean_object* v___f_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___f_821_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_822_ = lean_unsigned_to_nat(1u);
v___x_823_ = lean_nat_add(v_a_820_, v___x_822_);
lean_inc(v_m_819_);
lean_inc(v_a_820_);
v___x_824_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_821_, v_x_817_, v_a_820_, v_m_819_);
v___x_825_ = lean_apply_3(v_k_818_, v_a_820_, v___x_824_, v___x_823_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___redArg___boxed(lean_object* v_x_826_, lean_object* v_k_827_, lean_object* v_m_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_IR_NormalizeIds_withJP___redArg(v_x_826_, v_k_827_, v_m_828_, v_a_829_);
lean_dec(v_m_828_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP(lean_object* v_00_u03b1_831_, lean_object* v_x_832_, lean_object* v_k_833_, lean_object* v_m_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___f_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___f_836_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_837_ = lean_unsigned_to_nat(1u);
v___x_838_ = lean_nat_add(v_a_835_, v___x_837_);
lean_inc(v_m_834_);
lean_inc(v_a_835_);
v___x_839_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_836_, v_x_832_, v_a_835_, v_m_834_);
v___x_840_ = lean_apply_3(v_k_833_, v_a_835_, v___x_839_, v___x_838_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___boxed(lean_object* v_00_u03b1_841_, lean_object* v_x_842_, lean_object* v_k_843_, lean_object* v_m_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_IR_NormalizeIds_withJP(v_00_u03b1_841_, v_x_842_, v_k_843_, v_m_844_, v_a_845_);
lean_dec(v_m_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__0(lean_object* v_fst_847_, lean_object* v_x_848_){
_start:
{
lean_object* v_x_849_; uint8_t v_borrow_850_; lean_object* v_ty_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_859_; 
v_x_849_ = lean_ctor_get(v_x_848_, 0);
v_borrow_850_ = lean_ctor_get_uint8(v_x_848_, sizeof(void*)*2);
v_ty_851_ = lean_ctor_get(v_x_848_, 1);
v_isSharedCheck_859_ = !lean_is_exclusive(v_x_848_);
if (v_isSharedCheck_859_ == 0)
{
v___x_853_ = v_x_848_;
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_ty_851_);
lean_inc(v_x_849_);
lean_dec(v_x_848_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = l_Lean_IR_NormalizeIds_normIndex(v_x_849_, v_fst_847_);
lean_dec(v_x_849_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_855_);
v___x_857_ = v___x_853_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_ty_851_);
lean_ctor_set_uint8(v_reuseFailAlloc_858_, sizeof(void*)*2, v_borrow_850_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed(lean_object* v_fst_860_, lean_object* v_x_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_IR_NormalizeIds_withParams___redArg___lam__0(v_fst_860_, v_x_861_);
lean_dec(v_fst_860_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__2(lean_object* v___f_863_, lean_object* v_m_864_, lean_object* v_p_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_x_867_ = lean_ctor_get(v_p_865_, 0);
lean_inc(v_x_867_);
lean_dec_ref(v_p_865_);
v___x_868_ = lean_unsigned_to_nat(1u);
v___x_869_ = lean_nat_add(v___y_866_, v___x_868_);
v___x_870_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_863_, v_x_867_, v___y_866_, v_m_864_);
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___x_869_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg(lean_object* v_ps_874_, lean_object* v_k_875_, lean_object* v_m_876_, lean_object* v_a_877_){
_start:
{
lean_object* v___f_878_; lean_object* v___f_879_; lean_object* v___f_880_; lean_object* v___f_881_; lean_object* v___f_882_; lean_object* v___f_883_; lean_object* v___f_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v_fst_889_; lean_object* v_snd_890_; lean_object* v___f_896_; lean_object* v___f_897_; lean_object* v___f_898_; lean_object* v___f_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v___f_878_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__0));
v___f_879_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__1));
v___f_880_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__2));
v___f_881_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__3));
v___f_882_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__4));
v___f_883_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__5));
v___f_884_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__6));
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___f_878_);
lean_ctor_set(v___x_885_, 1, v___f_879_);
v___x_886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v___f_880_);
lean_ctor_set(v___x_886_, 2, v___f_881_);
lean_ctor_set(v___x_886_, 3, v___f_882_);
lean_ctor_set(v___x_886_, 4, v___f_883_);
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v___f_884_);
lean_inc_ref_n(v___x_887_, 7);
v___f_896_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_896_, 0, v___x_887_);
v___f_897_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_897_, 0, v___x_887_);
v___f_898_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_898_, 0, v___x_887_);
v___f_899_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_899_, 0, v___x_887_);
v___x_900_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_900_, 0, lean_box(0));
lean_closure_set(v___x_900_, 1, lean_box(0));
lean_closure_set(v___x_900_, 2, v___x_887_);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v___f_896_);
v___x_902_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_902_, 0, lean_box(0));
lean_closure_set(v___x_902_, 1, lean_box(0));
lean_closure_set(v___x_902_, 2, v___x_887_);
v___x_903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
lean_ctor_set(v___x_903_, 2, v___f_897_);
lean_ctor_set(v___x_903_, 3, v___f_898_);
lean_ctor_set(v___x_903_, 4, v___f_899_);
v___x_904_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_904_, 0, lean_box(0));
lean_closure_set(v___x_904_, 1, lean_box(0));
lean_closure_set(v___x_904_, 2, v___x_887_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_array_get_size(v_ps_874_);
v___x_908_ = lean_nat_dec_lt(v___x_906_, v___x_907_);
if (v___x_908_ == 0)
{
lean_dec_ref_known(v___x_905_, 2);
lean_inc(v_m_876_);
v_fst_889_ = v_m_876_;
v_snd_890_ = v_a_877_;
goto v___jp_888_;
}
else
{
lean_object* v___f_909_; size_t v___x_910_; size_t v___x_911_; lean_object* v___x_787__overap_912_; lean_object* v___x_913_; lean_object* v_fst_914_; lean_object* v_snd_915_; 
v___f_909_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__0));
v___x_910_ = ((size_t)0ULL);
v___x_911_ = lean_usize_of_nat(v___x_907_);
lean_inc(v_m_876_);
lean_inc_ref(v_ps_874_);
v___x_787__overap_912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_905_, v___f_909_, v_ps_874_, v___x_910_, v___x_911_, v_m_876_);
v___x_913_ = lean_apply_1(v___x_787__overap_912_, v_a_877_);
v_fst_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_fst_914_);
v_snd_915_ = lean_ctor_get(v___x_913_, 1);
lean_inc(v_snd_915_);
lean_dec_ref(v___x_913_);
v_fst_889_ = v_fst_914_;
v_snd_890_ = v_snd_915_;
goto v___jp_888_;
}
v___jp_888_:
{
lean_object* v___f_891_; size_t v_sz_892_; size_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
lean_inc(v_fst_889_);
v___f_891_ = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_891_, 0, v_fst_889_);
v_sz_892_ = lean_array_size(v_ps_874_);
v___x_893_ = ((size_t)0ULL);
v___x_894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_887_, v___f_891_, v_sz_892_, v___x_893_, v_ps_874_);
v___x_895_ = lean_apply_3(v_k_875_, v___x_894_, v_fst_889_, v_snd_890_);
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___boxed(lean_object* v_ps_916_, lean_object* v_k_917_, lean_object* v_m_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_IR_NormalizeIds_withParams___redArg(v_ps_916_, v_k_917_, v_m_918_, v_a_919_);
lean_dec(v_m_918_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams(lean_object* v_00_u03b1_921_, lean_object* v_ps_922_, lean_object* v_k_923_, lean_object* v_m_924_, lean_object* v_a_925_){
_start:
{
lean_object* v___f_926_; lean_object* v___f_927_; lean_object* v___f_928_; lean_object* v___f_929_; lean_object* v___f_930_; lean_object* v___f_931_; lean_object* v___f_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v_fst_937_; lean_object* v_snd_938_; lean_object* v___f_944_; lean_object* v___f_945_; lean_object* v___f_946_; lean_object* v___f_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v___f_926_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__0));
v___f_927_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__1));
v___f_928_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__2));
v___f_929_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__3));
v___f_930_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__4));
v___f_931_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__5));
v___f_932_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__6));
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v___f_926_);
lean_ctor_set(v___x_933_, 1, v___f_927_);
v___x_934_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___f_928_);
lean_ctor_set(v___x_934_, 2, v___f_929_);
lean_ctor_set(v___x_934_, 3, v___f_930_);
lean_ctor_set(v___x_934_, 4, v___f_931_);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v___f_932_);
lean_inc_ref_n(v___x_935_, 7);
v___f_944_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_944_, 0, v___x_935_);
v___f_945_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_945_, 0, v___x_935_);
v___f_946_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_946_, 0, v___x_935_);
v___f_947_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_947_, 0, v___x_935_);
v___x_948_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_948_, 0, lean_box(0));
lean_closure_set(v___x_948_, 1, lean_box(0));
lean_closure_set(v___x_948_, 2, v___x_935_);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v___f_944_);
v___x_950_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_950_, 0, lean_box(0));
lean_closure_set(v___x_950_, 1, lean_box(0));
lean_closure_set(v___x_950_, 2, v___x_935_);
v___x_951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_951_, 0, v___x_949_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
lean_ctor_set(v___x_951_, 2, v___f_945_);
lean_ctor_set(v___x_951_, 3, v___f_946_);
lean_ctor_set(v___x_951_, 4, v___f_947_);
v___x_952_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_952_, 0, lean_box(0));
lean_closure_set(v___x_952_, 1, lean_box(0));
lean_closure_set(v___x_952_, 2, v___x_935_);
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_951_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_unsigned_to_nat(0u);
v___x_955_ = lean_array_get_size(v_ps_922_);
v___x_956_ = lean_nat_dec_lt(v___x_954_, v___x_955_);
if (v___x_956_ == 0)
{
lean_dec_ref_known(v___x_953_, 2);
lean_inc(v_m_924_);
v_fst_937_ = v_m_924_;
v_snd_938_ = v_a_925_;
goto v___jp_936_;
}
else
{
lean_object* v___f_957_; size_t v___x_958_; size_t v___x_959_; lean_object* v___x_969__overap_960_; lean_object* v___x_961_; lean_object* v_fst_962_; lean_object* v_snd_963_; 
v___f_957_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__0));
v___x_958_ = ((size_t)0ULL);
v___x_959_ = lean_usize_of_nat(v___x_955_);
lean_inc(v_m_924_);
lean_inc_ref(v_ps_922_);
v___x_969__overap_960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_953_, v___f_957_, v_ps_922_, v___x_958_, v___x_959_, v_m_924_);
v___x_961_ = lean_apply_1(v___x_969__overap_960_, v_a_925_);
v_fst_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_fst_962_);
v_snd_963_ = lean_ctor_get(v___x_961_, 1);
lean_inc(v_snd_963_);
lean_dec_ref(v___x_961_);
v_fst_937_ = v_fst_962_;
v_snd_938_ = v_snd_963_;
goto v___jp_936_;
}
v___jp_936_:
{
lean_object* v___f_939_; size_t v_sz_940_; size_t v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
lean_inc(v_fst_937_);
v___f_939_ = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_939_, 0, v_fst_937_);
v_sz_940_ = lean_array_size(v_ps_922_);
v___x_941_ = ((size_t)0ULL);
v___x_942_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_935_, v___f_939_, v_sz_940_, v___x_941_, v_ps_922_);
v___x_943_ = lean_apply_3(v_k_923_, v___x_942_, v_fst_937_, v_snd_938_);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___boxed(lean_object* v_00_u03b1_964_, lean_object* v_ps_965_, lean_object* v_k_966_, lean_object* v_m_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_IR_NormalizeIds_withParams(v_00_u03b1_964_, v_ps_965_, v_k_966_, v_m_967_, v_a_968_);
lean_dec(v_m_967_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_instMonadLiftMN___lam__0(lean_object* v_00_u03b1_970_, lean_object* v_x_971_, lean_object* v_m_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_apply_1(v_x_971_, v_m_972_);
v___x_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v___y_973_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(lean_object* v_fst_978_, size_t v_sz_979_, size_t v_i_980_, lean_object* v_bs_981_){
_start:
{
uint8_t v___x_982_; 
v___x_982_ = lean_usize_dec_lt(v_i_980_, v_sz_979_);
if (v___x_982_ == 0)
{
return v_bs_981_;
}
else
{
lean_object* v_v_983_; lean_object* v_x_984_; uint8_t v_borrow_985_; lean_object* v_ty_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1000_; 
v_v_983_ = lean_array_uget(v_bs_981_, v_i_980_);
v_x_984_ = lean_ctor_get(v_v_983_, 0);
v_borrow_985_ = lean_ctor_get_uint8(v_v_983_, sizeof(void*)*2);
v_ty_986_ = lean_ctor_get(v_v_983_, 1);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_v_983_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_988_ = v_v_983_;
v_isShared_989_ = v_isSharedCheck_1000_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_ty_986_);
lean_inc(v_x_984_);
lean_dec(v_v_983_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1000_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v_bs_x27_991_; lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_990_ = lean_unsigned_to_nat(0u);
v_bs_x27_991_ = lean_array_uset(v_bs_981_, v_i_980_, v___x_990_);
v___x_992_ = l_Lean_IR_NormalizeIds_normIndex(v_x_984_, v_fst_978_);
lean_dec(v_x_984_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_992_);
v___x_994_ = v___x_988_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_ty_986_);
lean_ctor_set_uint8(v_reuseFailAlloc_999_, sizeof(void*)*2, v_borrow_985_);
v___x_994_ = v_reuseFailAlloc_999_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
size_t v___x_995_; size_t v___x_996_; lean_object* v___x_997_; 
v___x_995_ = ((size_t)1ULL);
v___x_996_ = lean_usize_add(v_i_980_, v___x_995_);
v___x_997_ = lean_array_uset(v_bs_x27_991_, v_i_980_, v___x_994_);
v_i_980_ = v___x_996_;
v_bs_981_ = v___x_997_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0___boxed(lean_object* v_fst_1001_, lean_object* v_sz_1002_, lean_object* v_i_1003_, lean_object* v_bs_1004_){
_start:
{
size_t v_sz_boxed_1005_; size_t v_i_boxed_1006_; lean_object* v_res_1007_; 
v_sz_boxed_1005_ = lean_unbox_usize(v_sz_1002_);
lean_dec(v_sz_1002_);
v_i_boxed_1006_ = lean_unbox_usize(v_i_1003_);
lean_dec(v_i_1003_);
v_res_1007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(v_fst_1001_, v_sz_boxed_1005_, v_i_boxed_1006_, v_bs_1004_);
lean_dec(v_fst_1001_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(lean_object* v_as_1008_, size_t v_i_1009_, size_t v_stop_1010_, lean_object* v_b_1011_, lean_object* v___y_1012_){
_start:
{
uint8_t v___x_1013_; 
v___x_1013_ = lean_usize_dec_eq(v_i_1009_, v_stop_1010_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; lean_object* v_x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; size_t v___x_1019_; size_t v___x_1020_; 
v___x_1014_ = lean_array_uget_borrowed(v_as_1008_, v_i_1009_);
v_x_1015_ = lean_ctor_get(v___x_1014_, 0);
v___x_1016_ = lean_unsigned_to_nat(1u);
v___x_1017_ = lean_nat_add(v___y_1012_, v___x_1016_);
lean_inc(v_x_1015_);
v___x_1018_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_x_1015_, v___y_1012_, v_b_1011_);
v___x_1019_ = ((size_t)1ULL);
v___x_1020_ = lean_usize_add(v_i_1009_, v___x_1019_);
v_i_1009_ = v___x_1020_;
v_b_1011_ = v___x_1018_;
v___y_1012_ = v___x_1017_;
goto _start;
}
else
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v_b_1011_);
lean_ctor_set(v___x_1022_, 1, v___y_1012_);
return v___x_1022_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1___boxed(lean_object* v_as_1023_, lean_object* v_i_1024_, lean_object* v_stop_1025_, lean_object* v_b_1026_, lean_object* v___y_1027_){
_start:
{
size_t v_i_boxed_1028_; size_t v_stop_boxed_1029_; lean_object* v_res_1030_; 
v_i_boxed_1028_ = lean_unbox_usize(v_i_1024_);
lean_dec(v_i_1024_);
v_stop_boxed_1029_ = lean_unbox_usize(v_stop_1025_);
lean_dec(v_stop_1025_);
v_res_1030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_as_1023_, v_i_boxed_1028_, v_stop_boxed_1029_, v_b_1026_, v___y_1027_);
lean_dec_ref(v_as_1023_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normFnBody(lean_object* v_x_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
switch(lean_obj_tag(v_x_1031_))
{
case 19:
{
lean_object* v_j_1034_; lean_object* v_xs_1035_; lean_object* v_v_1036_; lean_object* v_b_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1074_; 
v_j_1034_ = lean_ctor_get(v_x_1031_, 0);
v_xs_1035_ = lean_ctor_get(v_x_1031_, 1);
v_v_1036_ = lean_ctor_get(v_x_1031_, 2);
v_b_1037_ = lean_ctor_get(v_x_1031_, 3);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_x_1031_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1039_ = v_x_1031_;
v_isShared_1040_ = v_isSharedCheck_1074_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_b_1037_);
lean_inc(v_v_1036_);
lean_inc(v_xs_1035_);
lean_inc(v_j_1034_);
lean_dec(v_x_1031_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1074_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v_fst_1042_; lean_object* v_snd_1043_; lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = lean_array_get_size(v_xs_1035_);
v___x_1068_ = lean_nat_dec_lt(v___x_1066_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_inc(v_a_1032_);
v_fst_1042_ = v_a_1032_;
v_snd_1043_ = v_a_1033_;
goto v___jp_1041_;
}
else
{
size_t v___x_1069_; size_t v___x_1070_; lean_object* v___x_1071_; lean_object* v_fst_1072_; lean_object* v_snd_1073_; 
v___x_1069_ = ((size_t)0ULL);
v___x_1070_ = lean_usize_of_nat(v___x_1067_);
lean_inc(v_a_1032_);
v___x_1071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_1035_, v___x_1069_, v___x_1070_, v_a_1032_, v_a_1033_);
v_fst_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_fst_1072_);
v_snd_1073_ = lean_ctor_get(v___x_1071_, 1);
lean_inc(v_snd_1073_);
lean_dec_ref(v___x_1071_);
v_fst_1042_ = v_fst_1072_;
v_snd_1043_ = v_snd_1073_;
goto v___jp_1041_;
}
v___jp_1041_:
{
lean_object* v___x_1044_; lean_object* v_fst_1045_; lean_object* v_snd_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v_fst_1051_; lean_object* v_snd_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1065_; 
v___x_1044_ = l_Lean_IR_NormalizeIds_normFnBody(v_v_1036_, v_fst_1042_, v_snd_1043_);
v_fst_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_fst_1045_);
v_snd_1046_ = lean_ctor_get(v___x_1044_, 1);
lean_inc_n(v_snd_1046_, 2);
lean_dec_ref(v___x_1044_);
v___x_1047_ = lean_unsigned_to_nat(1u);
v___x_1048_ = lean_nat_add(v_snd_1046_, v___x_1047_);
lean_inc(v_a_1032_);
v___x_1049_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_j_1034_, v_snd_1046_, v_a_1032_);
v___x_1050_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1037_, v___x_1049_, v___x_1048_);
lean_dec(v___x_1049_);
v_fst_1051_ = lean_ctor_get(v___x_1050_, 0);
v_snd_1052_ = lean_ctor_get(v___x_1050_, 1);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1054_ = v___x_1050_;
v_isShared_1055_ = v_isSharedCheck_1065_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_snd_1052_);
lean_inc(v_fst_1051_);
lean_dec(v___x_1050_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1065_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
size_t v_sz_1056_; size_t v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v_sz_1056_ = lean_array_size(v_xs_1035_);
v___x_1057_ = ((size_t)0ULL);
v___x_1058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(v_fst_1042_, v_sz_1056_, v___x_1057_, v_xs_1035_);
lean_dec(v_fst_1042_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 3, v_fst_1051_);
lean_ctor_set(v___x_1039_, 2, v_fst_1045_);
lean_ctor_set(v___x_1039_, 1, v___x_1058_);
lean_ctor_set(v___x_1039_, 0, v_snd_1046_);
v___x_1060_ = v___x_1039_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(19, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_snd_1046_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v_fst_1045_);
lean_ctor_set(v_reuseFailAlloc_1064_, 3, v_fst_1051_);
v___x_1060_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1062_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1060_);
v___x_1062_ = v___x_1054_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_snd_1052_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
}
case 20:
{
lean_object* v_x_1075_; lean_object* v_i_1076_; lean_object* v_y_1077_; lean_object* v_b_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1097_; 
v_x_1075_ = lean_ctor_get(v_x_1031_, 0);
v_i_1076_ = lean_ctor_get(v_x_1031_, 1);
v_y_1077_ = lean_ctor_get(v_x_1031_, 2);
v_b_1078_ = lean_ctor_get(v_x_1031_, 3);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_x_1031_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1080_ = v_x_1031_;
v_isShared_1081_ = v_isSharedCheck_1097_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_b_1078_);
lean_inc(v_y_1077_);
lean_inc(v_i_1076_);
lean_inc(v_x_1075_);
lean_dec(v_x_1031_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1097_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v_fst_1085_; lean_object* v_snd_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1096_; 
v___x_1082_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1075_, v_a_1032_);
lean_dec(v_x_1075_);
v___x_1083_ = l_Lean_IR_NormalizeIds_normArg(v_y_1077_, v_a_1032_);
v___x_1084_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1078_, v_a_1032_, v_a_1033_);
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
v_reuseFailAlloc_1095_ = lean_alloc_ctor(20, 4, 0);
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
case 22:
{
lean_object* v_x_1098_; lean_object* v_i_1099_; lean_object* v_y_1100_; lean_object* v_b_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1120_; 
v_x_1098_ = lean_ctor_get(v_x_1031_, 0);
v_i_1099_ = lean_ctor_get(v_x_1031_, 1);
v_y_1100_ = lean_ctor_get(v_x_1031_, 2);
v_b_1101_ = lean_ctor_get(v_x_1031_, 3);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_x_1031_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1103_ = v_x_1031_;
v_isShared_1104_ = v_isSharedCheck_1120_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_b_1101_);
lean_inc(v_y_1100_);
lean_inc(v_i_1099_);
lean_inc(v_x_1098_);
lean_dec(v_x_1031_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1120_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v_fst_1108_; lean_object* v_snd_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1119_; 
v___x_1105_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1098_, v_a_1032_);
lean_dec(v_x_1098_);
v___x_1106_ = l_Lean_IR_NormalizeIds_normIndex(v_y_1100_, v_a_1032_);
lean_dec(v_y_1100_);
v___x_1107_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1101_, v_a_1032_, v_a_1033_);
v_fst_1108_ = lean_ctor_get(v___x_1107_, 0);
v_snd_1109_ = lean_ctor_get(v___x_1107_, 1);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1111_ = v___x_1107_;
v_isShared_1112_ = v_isSharedCheck_1119_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_snd_1109_);
lean_inc(v_fst_1108_);
lean_dec(v___x_1107_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1119_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 3, v_fst_1108_);
lean_ctor_set(v___x_1103_, 2, v___x_1106_);
lean_ctor_set(v___x_1103_, 0, v___x_1105_);
v___x_1114_ = v___x_1103_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(22, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_i_1099_);
lean_ctor_set(v_reuseFailAlloc_1118_, 2, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1118_, 3, v_fst_1108_);
v___x_1114_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1116_; 
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1114_);
v___x_1116_ = v___x_1111_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1114_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_snd_1109_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
case 23:
{
lean_object* v_x_1121_; lean_object* v_i_1122_; lean_object* v_offset_1123_; lean_object* v_y_1124_; lean_object* v_ty_1125_; lean_object* v_b_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1145_; 
v_x_1121_ = lean_ctor_get(v_x_1031_, 0);
v_i_1122_ = lean_ctor_get(v_x_1031_, 1);
v_offset_1123_ = lean_ctor_get(v_x_1031_, 2);
v_y_1124_ = lean_ctor_get(v_x_1031_, 3);
v_ty_1125_ = lean_ctor_get(v_x_1031_, 4);
v_b_1126_ = lean_ctor_get(v_x_1031_, 5);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_x_1031_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1128_ = v_x_1031_;
v_isShared_1129_ = v_isSharedCheck_1145_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_b_1126_);
lean_inc(v_ty_1125_);
lean_inc(v_y_1124_);
lean_inc(v_offset_1123_);
lean_inc(v_i_1122_);
lean_inc(v_x_1121_);
lean_dec(v_x_1031_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1145_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v_fst_1133_; lean_object* v_snd_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1144_; 
v___x_1130_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1121_, v_a_1032_);
lean_dec(v_x_1121_);
v___x_1131_ = l_Lean_IR_NormalizeIds_normIndex(v_y_1124_, v_a_1032_);
lean_dec(v_y_1124_);
v___x_1132_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1126_, v_a_1032_, v_a_1033_);
v_fst_1133_ = lean_ctor_get(v___x_1132_, 0);
v_snd_1134_ = lean_ctor_get(v___x_1132_, 1);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1136_ = v___x_1132_;
v_isShared_1137_ = v_isSharedCheck_1144_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_snd_1134_);
lean_inc(v_fst_1133_);
lean_dec(v___x_1132_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1144_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 5, v_fst_1133_);
lean_ctor_set(v___x_1128_, 3, v___x_1131_);
lean_ctor_set(v___x_1128_, 0, v___x_1130_);
v___x_1139_ = v___x_1128_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(23, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_i_1122_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_offset_1123_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1143_, 4, v_ty_1125_);
lean_ctor_set(v_reuseFailAlloc_1143_, 5, v_fst_1133_);
v___x_1139_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1141_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1139_);
v___x_1141_ = v___x_1136_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_snd_1134_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
case 21:
{
lean_object* v_x_1146_; lean_object* v_cidx_1147_; lean_object* v_b_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1166_; 
v_x_1146_ = lean_ctor_get(v_x_1031_, 0);
v_cidx_1147_ = lean_ctor_get(v_x_1031_, 1);
v_b_1148_ = lean_ctor_get(v_x_1031_, 2);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_x_1031_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1150_ = v_x_1031_;
v_isShared_1151_ = v_isSharedCheck_1166_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_b_1148_);
lean_inc(v_cidx_1147_);
lean_inc(v_x_1146_);
lean_dec(v_x_1031_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1166_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v_fst_1154_; lean_object* v_snd_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1165_; 
v___x_1152_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1146_, v_a_1032_);
lean_dec(v_x_1146_);
v___x_1153_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1148_, v_a_1032_, v_a_1033_);
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
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 2, v_fst_1154_);
lean_ctor_set(v___x_1150_, 0, v___x_1152_);
v___x_1160_ = v___x_1150_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(21, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_cidx_1147_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_fst_1154_);
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
case 24:
{
lean_object* v_x_1167_; lean_object* v_n_1168_; uint8_t v_c_1169_; uint8_t v_persistent_1170_; lean_object* v_b_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1189_; 
v_x_1167_ = lean_ctor_get(v_x_1031_, 0);
v_n_1168_ = lean_ctor_get(v_x_1031_, 1);
v_c_1169_ = lean_ctor_get_uint8(v_x_1031_, sizeof(void*)*3);
v_persistent_1170_ = lean_ctor_get_uint8(v_x_1031_, sizeof(void*)*3 + 1);
v_b_1171_ = lean_ctor_get(v_x_1031_, 2);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_x_1031_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1173_ = v_x_1031_;
v_isShared_1174_ = v_isSharedCheck_1189_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_b_1171_);
lean_inc(v_n_1168_);
lean_inc(v_x_1167_);
lean_dec(v_x_1031_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1189_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v_fst_1177_; lean_object* v_snd_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1188_; 
v___x_1175_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1167_, v_a_1032_);
lean_dec(v_x_1167_);
v___x_1176_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1171_, v_a_1032_, v_a_1033_);
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
v_reuseFailAlloc_1187_ = lean_alloc_ctor(24, 3, 2);
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
case 25:
{
lean_object* v_x_1190_; lean_object* v_n_1191_; uint8_t v_c_1192_; uint8_t v_persistent_1193_; lean_object* v_b_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1212_; 
v_x_1190_ = lean_ctor_get(v_x_1031_, 0);
v_n_1191_ = lean_ctor_get(v_x_1031_, 1);
v_c_1192_ = lean_ctor_get_uint8(v_x_1031_, sizeof(void*)*3);
v_persistent_1193_ = lean_ctor_get_uint8(v_x_1031_, sizeof(void*)*3 + 1);
v_b_1194_ = lean_ctor_get(v_x_1031_, 2);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_x_1031_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1196_ = v_x_1031_;
v_isShared_1197_ = v_isSharedCheck_1212_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_b_1194_);
lean_inc(v_n_1191_);
lean_inc(v_x_1190_);
lean_dec(v_x_1031_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1212_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v_fst_1200_; lean_object* v_snd_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1211_; 
v___x_1198_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1190_, v_a_1032_);
lean_dec(v_x_1190_);
v___x_1199_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1194_, v_a_1032_, v_a_1033_);
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
v_reuseFailAlloc_1210_ = lean_alloc_ctor(25, 3, 2);
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
case 26:
{
lean_object* v_x_1213_; lean_object* v_b_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1232_; 
v_x_1213_ = lean_ctor_get(v_x_1031_, 0);
v_b_1214_ = lean_ctor_get(v_x_1031_, 1);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_x_1031_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1216_ = v_x_1031_;
v_isShared_1217_ = v_isSharedCheck_1232_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_b_1214_);
lean_inc(v_x_1213_);
lean_dec(v_x_1031_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1232_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v_fst_1220_; lean_object* v_snd_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1231_; 
v___x_1218_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1213_, v_a_1032_);
lean_dec(v_x_1213_);
v___x_1219_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1214_, v_a_1032_, v_a_1033_);
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
v_reuseFailAlloc_1230_ = lean_alloc_ctor(26, 2, 0);
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
case 27:
{
lean_object* v_tid_1233_; lean_object* v_x_1234_; lean_object* v_xType_1235_; lean_object* v_cs_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1256_; 
v_tid_1233_ = lean_ctor_get(v_x_1031_, 0);
v_x_1234_ = lean_ctor_get(v_x_1031_, 1);
v_xType_1235_ = lean_ctor_get(v_x_1031_, 2);
v_cs_1236_ = lean_ctor_get(v_x_1031_, 3);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_x_1031_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1238_ = v_x_1031_;
v_isShared_1239_ = v_isSharedCheck_1256_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_cs_1236_);
lean_inc(v_xType_1235_);
lean_inc(v_x_1234_);
lean_inc(v_tid_1233_);
lean_dec(v_x_1031_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1256_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; size_t v_sz_1241_; size_t v___x_1242_; lean_object* v___x_1243_; lean_object* v_fst_1244_; lean_object* v_snd_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1255_; 
v___x_1240_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1234_, v_a_1032_);
lean_dec(v_x_1234_);
v_sz_1241_ = lean_array_size(v_cs_1236_);
v___x_1242_ = ((size_t)0ULL);
v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(v_sz_1241_, v___x_1242_, v_cs_1236_, v_a_1032_, v_a_1033_);
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
v_reuseFailAlloc_1254_ = lean_alloc_ctor(27, 4, 0);
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
case 29:
{
lean_object* v_j_1257_; lean_object* v_ys_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1268_; 
v_j_1257_ = lean_ctor_get(v_x_1031_, 0);
v_ys_1258_ = lean_ctor_get(v_x_1031_, 1);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_x_1031_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1260_ = v_x_1031_;
v_isShared_1261_ = v_isSharedCheck_1268_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_ys_1258_);
lean_inc(v_j_1257_);
lean_dec(v_x_1031_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1268_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1262_ = l_Lean_IR_NormalizeIds_normIndex(v_j_1257_, v_a_1032_);
lean_dec(v_j_1257_);
v___x_1263_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_1258_, v_a_1032_);
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
v_reuseFailAlloc_1267_ = lean_alloc_ctor(29, 2, 0);
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
lean_ctor_set(v___x_1266_, 1, v_a_1033_);
return v___x_1266_;
}
}
}
case 28:
{
lean_object* v_x_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1278_; 
v_x_1269_ = lean_ctor_get(v_x_1031_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_x_1031_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1271_ = v_x_1031_;
v_isShared_1272_ = v_isSharedCheck_1278_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_x_1269_);
lean_dec(v_x_1031_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1278_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1273_ = l_Lean_IR_NormalizeIds_normArg(v_x_1269_, v_a_1032_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___x_1273_);
v___x_1275_ = v___x_1271_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(28, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set(v___x_1276_, 1, v_a_1033_);
return v___x_1276_;
}
}
}
case 30:
{
lean_object* v___x_1279_; 
v___x_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1279_, 0, v_x_1031_);
lean_ctor_set(v___x_1279_, 1, v_a_1033_);
return v___x_1279_;
}
default: 
{
lean_object* v_x_1280_; lean_object* v_b_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v_fst_1286_; lean_object* v_snd_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1297_; 
v_x_1280_ = l_Lean_IR_FnBody_targetVar(v_x_1031_);
v_b_1281_ = l_Lean_IR_FnBody_body(v_x_1031_);
v___x_1282_ = lean_unsigned_to_nat(1u);
v___x_1283_ = lean_nat_add(v_a_1033_, v___x_1282_);
lean_inc(v_a_1032_);
lean_inc(v_a_1033_);
v___x_1284_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_x_1280_, v_a_1033_, v_a_1032_);
v___x_1285_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1281_, v___x_1284_, v___x_1283_);
lean_dec(v___x_1284_);
v_fst_1286_ = lean_ctor_get(v___x_1285_, 0);
v_snd_1287_ = lean_ctor_get(v___x_1285_, 1);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1289_ = v___x_1285_;
v_isShared_1290_ = v_isSharedCheck_1297_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_snd_1287_);
lean_inc(v_fst_1286_);
lean_dec(v___x_1285_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1297_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1295_; 
v___x_1291_ = l_Lean_IR_NormalizeIds_normExpr(v_x_1031_, v_a_1032_);
v___x_1292_ = l_Lean_IR_FnBody_setTargetVar(v___x_1291_, v_a_1033_);
v___x_1293_ = l_Lean_IR_FnBody_setBody(v___x_1292_, v_fst_1286_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1293_);
v___x_1295_ = v___x_1289_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_snd_1287_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(size_t v_sz_1298_, size_t v_i_1299_, lean_object* v_bs_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
uint8_t v___x_1303_; 
v___x_1303_ = lean_usize_dec_lt(v_i_1299_, v_sz_1298_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; 
v___x_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1304_, 0, v_bs_1300_);
lean_ctor_set(v___x_1304_, 1, v___y_1302_);
return v___x_1304_;
}
else
{
lean_object* v_v_1305_; lean_object* v___x_1306_; lean_object* v_bs_x27_1307_; lean_object* v_fst_1309_; lean_object* v_snd_1310_; 
v_v_1305_ = lean_array_uget(v_bs_1300_, v_i_1299_);
v___x_1306_ = lean_unsigned_to_nat(0u);
v_bs_x27_1307_ = lean_array_uset(v_bs_1300_, v_i_1299_, v___x_1306_);
if (lean_obj_tag(v_v_1305_) == 0)
{
lean_object* v_info_1315_; lean_object* v_b_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1326_; 
v_info_1315_ = lean_ctor_get(v_v_1305_, 0);
v_b_1316_ = lean_ctor_get(v_v_1305_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_v_1305_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1318_ = v_v_1305_;
v_isShared_1319_ = v_isSharedCheck_1326_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_b_1316_);
lean_inc(v_info_1315_);
lean_dec(v_v_1305_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1326_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v_fst_1321_; lean_object* v_snd_1322_; lean_object* v___x_1324_; 
v___x_1320_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1316_, v___y_1301_, v___y_1302_);
v_fst_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_fst_1321_);
v_snd_1322_ = lean_ctor_get(v___x_1320_, 1);
lean_inc(v_snd_1322_);
lean_dec_ref(v___x_1320_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 1, v_fst_1321_);
v___x_1324_ = v___x_1318_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_info_1315_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v_fst_1321_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
v_fst_1309_ = v___x_1324_;
v_snd_1310_ = v_snd_1322_;
goto v___jp_1308_;
}
}
}
else
{
lean_object* v_b_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1337_; 
v_b_1327_ = lean_ctor_get(v_v_1305_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_v_1305_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1329_ = v_v_1305_;
v_isShared_1330_ = v_isSharedCheck_1337_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_b_1327_);
lean_dec(v_v_1305_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1337_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; lean_object* v_fst_1332_; lean_object* v_snd_1333_; lean_object* v___x_1335_; 
v___x_1331_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1327_, v___y_1301_, v___y_1302_);
v_fst_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_fst_1332_);
v_snd_1333_ = lean_ctor_get(v___x_1331_, 1);
lean_inc(v_snd_1333_);
lean_dec_ref(v___x_1331_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v_fst_1332_);
v___x_1335_ = v___x_1329_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_fst_1332_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
v_fst_1309_ = v___x_1335_;
v_snd_1310_ = v_snd_1333_;
goto v___jp_1308_;
}
}
}
v___jp_1308_:
{
size_t v___x_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = ((size_t)1ULL);
v___x_1312_ = lean_usize_add(v_i_1299_, v___x_1311_);
v___x_1313_ = lean_array_uset(v_bs_x27_1307_, v_i_1299_, v_fst_1309_);
v_i_1299_ = v___x_1312_;
v_bs_1300_ = v___x_1313_;
v___y_1302_ = v_snd_1310_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2___boxed(lean_object* v_sz_1338_, lean_object* v_i_1339_, lean_object* v_bs_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
size_t v_sz_boxed_1343_; size_t v_i_boxed_1344_; lean_object* v_res_1345_; 
v_sz_boxed_1343_ = lean_unbox_usize(v_sz_1338_);
lean_dec(v_sz_1338_);
v_i_boxed_1344_ = lean_unbox_usize(v_i_1339_);
lean_dec(v_i_1339_);
v_res_1345_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(v_sz_boxed_1343_, v_i_boxed_1344_, v_bs_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1341_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normFnBody___boxed(lean_object* v_x_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_IR_NormalizeIds_normFnBody(v_x_1346_, v_a_1347_, v_a_1348_);
lean_dec(v_a_1347_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normDecl(lean_object* v_d_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
if (lean_obj_tag(v_d_1350_) == 0)
{
lean_object* v_xs_1353_; lean_object* v_body_1354_; lean_object* v_fst_1356_; lean_object* v_snd_1357_; lean_object* v___x_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v_xs_1353_ = lean_ctor_get(v_d_1350_, 1);
v_body_1354_ = lean_ctor_get(v_d_1350_, 3);
v___x_1369_ = lean_unsigned_to_nat(0u);
v___x_1370_ = lean_array_get_size(v_xs_1353_);
v___x_1371_ = lean_nat_dec_lt(v___x_1369_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_inc(v_a_1351_);
v_fst_1356_ = v_a_1351_;
v_snd_1357_ = v_a_1352_;
goto v___jp_1355_;
}
else
{
size_t v___x_1372_; size_t v___x_1373_; lean_object* v___x_1374_; lean_object* v_fst_1375_; lean_object* v_snd_1376_; 
v___x_1372_ = ((size_t)0ULL);
v___x_1373_ = lean_usize_of_nat(v___x_1370_);
lean_inc(v_a_1351_);
v___x_1374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_1353_, v___x_1372_, v___x_1373_, v_a_1351_, v_a_1352_);
v_fst_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_fst_1375_);
v_snd_1376_ = lean_ctor_get(v___x_1374_, 1);
lean_inc(v_snd_1376_);
lean_dec_ref(v___x_1374_);
v_fst_1356_ = v_fst_1375_;
v_snd_1357_ = v_snd_1376_;
goto v___jp_1355_;
}
v___jp_1355_:
{
lean_object* v___x_1358_; lean_object* v_fst_1359_; lean_object* v_snd_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1368_; 
lean_inc(v_body_1354_);
v___x_1358_ = l_Lean_IR_NormalizeIds_normFnBody(v_body_1354_, v_fst_1356_, v_snd_1357_);
lean_dec(v_fst_1356_);
v_fst_1359_ = lean_ctor_get(v___x_1358_, 0);
v_snd_1360_ = lean_ctor_get(v___x_1358_, 1);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1362_ = v___x_1358_;
v_isShared_1363_ = v_isSharedCheck_1368_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_snd_1360_);
lean_inc(v_fst_1359_);
lean_dec(v___x_1358_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1368_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1364_ = l_Lean_IR_Decl_updateBody_x21(v_d_1350_, v_fst_1359_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1364_);
v___x_1366_ = v___x_1362_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_snd_1360_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
else
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v_d_1350_);
lean_ctor_set(v___x_1377_, 1, v_a_1352_);
return v___x_1377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normDecl___boxed(lean_object* v_d_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_IR_NormalizeIds_normDecl(v_d_1378_, v_a_1379_, v_a_1380_);
lean_dec(v_a_1379_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_normalizeIds(lean_object* v_d_1382_){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v_fst_1386_; 
v___x_1383_ = lean_box(1);
v___x_1384_ = lean_unsigned_to_nat(1u);
v___x_1385_ = l_Lean_IR_NormalizeIds_normDecl(v_d_1382_, v___x_1383_, v___x_1384_);
v_fst_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_fst_1386_);
lean_dec_ref(v___x_1385_);
return v_fst_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArg(lean_object* v_f_1387_, lean_object* v_x_1388_){
_start:
{
if (lean_obj_tag(v_x_1388_) == 0)
{
lean_object* v_id_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1397_; 
v_id_1389_ = lean_ctor_get(v_x_1388_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_x_1388_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1391_ = v_x_1388_;
v_isShared_1392_ = v_isSharedCheck_1397_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_id_1389_);
lean_dec(v_x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1397_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1393_ = lean_apply_1(v_f_1387_, v_id_1389_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1393_);
v___x_1395_ = v___x_1391_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
else
{
lean_dec_ref(v_f_1387_);
return v_x_1388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(lean_object* v_f_1398_, size_t v_sz_1399_, size_t v_i_1400_, lean_object* v_bs_1401_){
_start:
{
uint8_t v___x_1402_; 
v___x_1402_ = lean_usize_dec_lt(v_i_1400_, v_sz_1399_);
if (v___x_1402_ == 0)
{
lean_dec_ref(v_f_1398_);
return v_bs_1401_;
}
else
{
lean_object* v_v_1403_; lean_object* v___x_1404_; lean_object* v_bs_x27_1405_; lean_object* v___y_1407_; 
v_v_1403_ = lean_array_uget(v_bs_1401_, v_i_1400_);
v___x_1404_ = lean_unsigned_to_nat(0u);
v_bs_x27_1405_ = lean_array_uset(v_bs_1401_, v_i_1400_, v___x_1404_);
if (lean_obj_tag(v_v_1403_) == 0)
{
lean_object* v_id_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1420_; 
v_id_1412_ = lean_ctor_get(v_v_1403_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_v_1403_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1414_ = v_v_1403_;
v_isShared_1415_ = v_isSharedCheck_1420_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_id_1412_);
lean_dec(v_v_1403_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1420_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
lean_inc_ref(v_f_1398_);
v___x_1416_ = lean_apply_1(v_f_1398_, v_id_1412_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1416_);
v___x_1418_ = v___x_1414_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
v___y_1407_ = v___x_1418_;
goto v___jp_1406_;
}
}
}
else
{
v___y_1407_ = v_v_1403_;
goto v___jp_1406_;
}
v___jp_1406_:
{
size_t v___x_1408_; size_t v___x_1409_; lean_object* v___x_1410_; 
v___x_1408_ = ((size_t)1ULL);
v___x_1409_ = lean_usize_add(v_i_1400_, v___x_1408_);
v___x_1410_ = lean_array_uset(v_bs_x27_1405_, v_i_1400_, v___y_1407_);
v_i_1400_ = v___x_1409_;
v_bs_1401_ = v___x_1410_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0___boxed(lean_object* v_f_1421_, lean_object* v_sz_1422_, lean_object* v_i_1423_, lean_object* v_bs_1424_){
_start:
{
size_t v_sz_boxed_1425_; size_t v_i_boxed_1426_; lean_object* v_res_1427_; 
v_sz_boxed_1425_ = lean_unbox_usize(v_sz_1422_);
lean_dec(v_sz_1422_);
v_i_boxed_1426_ = lean_unbox_usize(v_i_1423_);
lean_dec(v_i_1423_);
v_res_1427_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(v_f_1421_, v_sz_boxed_1425_, v_i_boxed_1426_, v_bs_1424_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArgs(lean_object* v_f_1428_, lean_object* v_as_1429_){
_start:
{
size_t v_sz_1430_; size_t v___x_1431_; lean_object* v___x_1432_; 
v_sz_1430_ = lean_array_size(v_as_1429_);
v___x_1431_ = ((size_t)0ULL);
v___x_1432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(v_f_1428_, v_sz_1430_, v___x_1431_, v_as_1429_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapFnBody(lean_object* v_f_1433_, lean_object* v_x_1434_){
_start:
{
switch(lean_obj_tag(v_x_1434_))
{
case 0:
{
lean_object* v_tgt_1435_; lean_object* v_b_1436_; lean_object* v_i_1437_; lean_object* v_ys_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1447_; 
v_tgt_1435_ = lean_ctor_get(v_x_1434_, 0);
v_b_1436_ = lean_ctor_get(v_x_1434_, 1);
v_i_1437_ = lean_ctor_get(v_x_1434_, 2);
v_ys_1438_ = lean_ctor_get(v_x_1434_, 3);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1440_ = v_x_1434_;
v_isShared_1441_ = v_isSharedCheck_1447_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_ys_1438_);
lean_inc(v_i_1437_);
lean_inc(v_b_1436_);
lean_inc(v_tgt_1435_);
lean_dec(v_x_1434_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1447_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1445_; 
lean_inc_ref(v_f_1433_);
v___x_1442_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1436_);
v___x_1443_ = l_Lean_IR_MapVars_mapArgs(v_f_1433_, v_ys_1438_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 3, v___x_1443_);
lean_ctor_set(v___x_1440_, 1, v___x_1442_);
v___x_1445_ = v___x_1440_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_tgt_1435_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1446_, 2, v_i_1437_);
lean_ctor_set(v_reuseFailAlloc_1446_, 3, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
case 1:
{
lean_object* v_tgt_1448_; lean_object* v_b_1449_; lean_object* v_n_1450_; lean_object* v_x_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1460_; 
v_tgt_1448_ = lean_ctor_get(v_x_1434_, 0);
v_b_1449_ = lean_ctor_get(v_x_1434_, 1);
v_n_1450_ = lean_ctor_get(v_x_1434_, 2);
v_x_1451_ = lean_ctor_get(v_x_1434_, 3);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1453_ = v_x_1434_;
v_isShared_1454_ = v_isSharedCheck_1460_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_x_1451_);
lean_inc(v_n_1450_);
lean_inc(v_b_1449_);
lean_inc(v_tgt_1448_);
lean_dec(v_x_1434_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1460_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
lean_inc_ref(v_f_1433_);
v___x_1455_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1449_);
v___x_1456_ = lean_apply_1(v_f_1433_, v_x_1451_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 3, v___x_1456_);
lean_ctor_set(v___x_1453_, 1, v___x_1455_);
v___x_1458_ = v___x_1453_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_tgt_1448_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1459_, 2, v_n_1450_);
lean_ctor_set(v_reuseFailAlloc_1459_, 3, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
case 2:
{
lean_object* v_tgt_1461_; lean_object* v_b_1462_; lean_object* v_x_1463_; lean_object* v_i_1464_; uint8_t v_updtHeader_1465_; lean_object* v_ys_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1476_; 
v_tgt_1461_ = lean_ctor_get(v_x_1434_, 0);
v_b_1462_ = lean_ctor_get(v_x_1434_, 1);
v_x_1463_ = lean_ctor_get(v_x_1434_, 2);
v_i_1464_ = lean_ctor_get(v_x_1434_, 3);
v_updtHeader_1465_ = lean_ctor_get_uint8(v_x_1434_, sizeof(void*)*5);
v_ys_1466_ = lean_ctor_get(v_x_1434_, 4);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1468_ = v_x_1434_;
v_isShared_1469_ = v_isSharedCheck_1476_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_ys_1466_);
lean_inc(v_i_1464_);
lean_inc(v_x_1463_);
lean_inc(v_b_1462_);
lean_inc(v_tgt_1461_);
lean_dec(v_x_1434_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1476_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1474_; 
lean_inc_ref_n(v_f_1433_, 2);
v___x_1470_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1462_);
v___x_1471_ = lean_apply_1(v_f_1433_, v_x_1463_);
v___x_1472_ = l_Lean_IR_MapVars_mapArgs(v_f_1433_, v_ys_1466_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 4, v___x_1472_);
lean_ctor_set(v___x_1468_, 2, v___x_1471_);
lean_ctor_set(v___x_1468_, 1, v___x_1470_);
v___x_1474_ = v___x_1468_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(2, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_tgt_1461_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v___x_1470_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v_i_1464_);
lean_ctor_set(v_reuseFailAlloc_1475_, 4, v___x_1472_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*5, v_updtHeader_1465_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
case 3:
{
lean_object* v_tgt_1477_; lean_object* v_b_1478_; lean_object* v_i_1479_; lean_object* v_x_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1489_; 
v_tgt_1477_ = lean_ctor_get(v_x_1434_, 0);
v_b_1478_ = lean_ctor_get(v_x_1434_, 1);
v_i_1479_ = lean_ctor_get(v_x_1434_, 2);
v_x_1480_ = lean_ctor_get(v_x_1434_, 3);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1482_ = v_x_1434_;
v_isShared_1483_ = v_isSharedCheck_1489_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_x_1480_);
lean_inc(v_i_1479_);
lean_inc(v_b_1478_);
lean_inc(v_tgt_1477_);
lean_dec(v_x_1434_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1489_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
lean_inc_ref(v_f_1433_);
v___x_1484_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1478_);
v___x_1485_ = lean_apply_1(v_f_1433_, v_x_1480_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 3, v___x_1485_);
lean_ctor_set(v___x_1482_, 1, v___x_1484_);
v___x_1487_ = v___x_1482_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_tgt_1477_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v_i_1479_);
lean_ctor_set(v_reuseFailAlloc_1488_, 3, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
case 4:
{
lean_object* v_tgt_1490_; lean_object* v_b_1491_; lean_object* v_i_1492_; lean_object* v_x_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1502_; 
v_tgt_1490_ = lean_ctor_get(v_x_1434_, 0);
v_b_1491_ = lean_ctor_get(v_x_1434_, 1);
v_i_1492_ = lean_ctor_get(v_x_1434_, 2);
v_x_1493_ = lean_ctor_get(v_x_1434_, 3);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1495_ = v_x_1434_;
v_isShared_1496_ = v_isSharedCheck_1502_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_x_1493_);
lean_inc(v_i_1492_);
lean_inc(v_b_1491_);
lean_inc(v_tgt_1490_);
lean_dec(v_x_1434_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1502_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1500_; 
lean_inc_ref(v_f_1433_);
v___x_1497_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1491_);
v___x_1498_ = lean_apply_1(v_f_1433_, v_x_1493_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 3, v___x_1498_);
lean_ctor_set(v___x_1495_, 1, v___x_1497_);
v___x_1500_ = v___x_1495_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_tgt_1490_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_i_1492_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
case 5:
{
lean_object* v_tgt_1503_; lean_object* v_b_1504_; lean_object* v_ty_1505_; lean_object* v_n_1506_; lean_object* v_offset_1507_; lean_object* v_x_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1517_; 
v_tgt_1503_ = lean_ctor_get(v_x_1434_, 0);
v_b_1504_ = lean_ctor_get(v_x_1434_, 1);
v_ty_1505_ = lean_ctor_get(v_x_1434_, 2);
v_n_1506_ = lean_ctor_get(v_x_1434_, 3);
v_offset_1507_ = lean_ctor_get(v_x_1434_, 4);
v_x_1508_ = lean_ctor_get(v_x_1434_, 5);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1510_ = v_x_1434_;
v_isShared_1511_ = v_isSharedCheck_1517_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_x_1508_);
lean_inc(v_offset_1507_);
lean_inc(v_n_1506_);
lean_inc(v_ty_1505_);
lean_inc(v_b_1504_);
lean_inc(v_tgt_1503_);
lean_dec(v_x_1434_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1517_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
lean_inc_ref(v_f_1433_);
v___x_1512_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1504_);
v___x_1513_ = lean_apply_1(v_f_1433_, v_x_1508_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 5, v___x_1513_);
lean_ctor_set(v___x_1510_, 1, v___x_1512_);
v___x_1515_ = v___x_1510_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_tgt_1503_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v_ty_1505_);
lean_ctor_set(v_reuseFailAlloc_1516_, 3, v_n_1506_);
lean_ctor_set(v_reuseFailAlloc_1516_, 4, v_offset_1507_);
lean_ctor_set(v_reuseFailAlloc_1516_, 5, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
case 6:
{
lean_object* v_tgt_1518_; lean_object* v_b_1519_; lean_object* v_ty_1520_; lean_object* v_c_1521_; lean_object* v_ys_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1531_; 
v_tgt_1518_ = lean_ctor_get(v_x_1434_, 0);
v_b_1519_ = lean_ctor_get(v_x_1434_, 1);
v_ty_1520_ = lean_ctor_get(v_x_1434_, 2);
v_c_1521_ = lean_ctor_get(v_x_1434_, 3);
v_ys_1522_ = lean_ctor_get(v_x_1434_, 4);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1524_ = v_x_1434_;
v_isShared_1525_ = v_isSharedCheck_1531_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_ys_1522_);
lean_inc(v_c_1521_);
lean_inc(v_ty_1520_);
lean_inc(v_b_1519_);
lean_inc(v_tgt_1518_);
lean_dec(v_x_1434_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1531_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1529_; 
lean_inc_ref(v_f_1433_);
v___x_1526_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1519_);
v___x_1527_ = l_Lean_IR_MapVars_mapArgs(v_f_1433_, v_ys_1522_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 4, v___x_1527_);
lean_ctor_set(v___x_1524_, 1, v___x_1526_);
v___x_1529_ = v___x_1524_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(6, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_tgt_1518_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_ty_1520_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_c_1521_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
case 7:
{
lean_object* v_tgt_1532_; lean_object* v_b_1533_; lean_object* v_c_1534_; lean_object* v_ys_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1544_; 
v_tgt_1532_ = lean_ctor_get(v_x_1434_, 0);
v_b_1533_ = lean_ctor_get(v_x_1434_, 1);
v_c_1534_ = lean_ctor_get(v_x_1434_, 2);
v_ys_1535_ = lean_ctor_get(v_x_1434_, 3);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1537_ = v_x_1434_;
v_isShared_1538_ = v_isSharedCheck_1544_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_ys_1535_);
lean_inc(v_c_1534_);
lean_inc(v_b_1533_);
lean_inc(v_tgt_1532_);
lean_dec(v_x_1434_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1544_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
lean_inc_ref(v_f_1433_);
v___x_1539_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1533_);
v___x_1540_ = l_Lean_IR_MapVars_mapArgs(v_f_1433_, v_ys_1535_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 3, v___x_1540_);
lean_ctor_set(v___x_1537_, 1, v___x_1539_);
v___x_1542_ = v___x_1537_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_tgt_1532_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_c_1534_);
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
case 8:
{
lean_object* v_tgt_1545_; lean_object* v_b_1546_; lean_object* v_x_1547_; lean_object* v_ys_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1558_; 
v_tgt_1545_ = lean_ctor_get(v_x_1434_, 0);
v_b_1546_ = lean_ctor_get(v_x_1434_, 1);
v_x_1547_ = lean_ctor_get(v_x_1434_, 2);
v_ys_1548_ = lean_ctor_get(v_x_1434_, 3);
v_isSharedCheck_1558_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1550_ = v_x_1434_;
v_isShared_1551_ = v_isSharedCheck_1558_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_ys_1548_);
lean_inc(v_x_1547_);
lean_inc(v_b_1546_);
lean_inc(v_tgt_1545_);
lean_dec(v_x_1434_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1558_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1556_; 
lean_inc_ref_n(v_f_1433_, 2);
v___x_1552_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1546_);
v___x_1553_ = lean_apply_1(v_f_1433_, v_x_1547_);
v___x_1554_ = l_Lean_IR_MapVars_mapArgs(v_f_1433_, v_ys_1548_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 3, v___x_1554_);
lean_ctor_set(v___x_1550_, 2, v___x_1553_);
lean_ctor_set(v___x_1550_, 1, v___x_1552_);
v___x_1556_ = v___x_1550_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_tgt_1545_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1557_, 2, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1557_, 3, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
case 9:
{
lean_object* v_tgt_1559_; lean_object* v_b_1560_; lean_object* v_ty_1561_; lean_object* v_x_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1571_; 
v_tgt_1559_ = lean_ctor_get(v_x_1434_, 0);
v_b_1560_ = lean_ctor_get(v_x_1434_, 1);
v_ty_1561_ = lean_ctor_get(v_x_1434_, 2);
v_x_1562_ = lean_ctor_get(v_x_1434_, 3);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1564_ = v_x_1434_;
v_isShared_1565_ = v_isSharedCheck_1571_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_x_1562_);
lean_inc(v_ty_1561_);
lean_inc(v_b_1560_);
lean_inc(v_tgt_1559_);
lean_dec(v_x_1434_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1571_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; 
lean_inc_ref(v_f_1433_);
v___x_1566_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1560_);
v___x_1567_ = lean_apply_1(v_f_1433_, v_x_1562_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 3, v___x_1567_);
lean_ctor_set(v___x_1564_, 1, v___x_1566_);
v___x_1569_ = v___x_1564_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_tgt_1559_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1570_, 2, v_ty_1561_);
lean_ctor_set(v_reuseFailAlloc_1570_, 3, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
case 10:
{
lean_object* v_tgt_1572_; lean_object* v_b_1573_; lean_object* v_ty_1574_; lean_object* v_x_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1584_; 
v_tgt_1572_ = lean_ctor_get(v_x_1434_, 0);
v_b_1573_ = lean_ctor_get(v_x_1434_, 1);
v_ty_1574_ = lean_ctor_get(v_x_1434_, 2);
v_x_1575_ = lean_ctor_get(v_x_1434_, 3);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1577_ = v_x_1434_;
v_isShared_1578_ = v_isSharedCheck_1584_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_x_1575_);
lean_inc(v_ty_1574_);
lean_inc(v_b_1573_);
lean_inc(v_tgt_1572_);
lean_dec(v_x_1434_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1584_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1582_; 
lean_inc_ref(v_f_1433_);
v___x_1579_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1573_);
v___x_1580_ = lean_apply_1(v_f_1433_, v_x_1575_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 3, v___x_1580_);
lean_ctor_set(v___x_1577_, 1, v___x_1579_);
v___x_1582_ = v___x_1577_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_tgt_1572_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1583_, 2, v_ty_1574_);
lean_ctor_set(v_reuseFailAlloc_1583_, 3, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
case 11:
{
lean_object* v_tgt_1585_; lean_object* v_b_1586_; uint8_t v_v_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1595_; 
v_tgt_1585_ = lean_ctor_get(v_x_1434_, 0);
v_b_1586_ = lean_ctor_get(v_x_1434_, 1);
v_v_1587_ = lean_ctor_get_uint8(v_x_1434_, sizeof(void*)*2);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1589_ = v_x_1434_;
v_isShared_1590_ = v_isSharedCheck_1595_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_b_1586_);
lean_inc(v_tgt_1585_);
lean_dec(v_x_1434_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1595_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1591_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1586_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 1, v___x_1591_);
v___x_1593_ = v___x_1589_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(11, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_tgt_1585_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v___x_1591_);
lean_ctor_set_uint8(v_reuseFailAlloc_1594_, sizeof(void*)*2, v_v_1587_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
case 12:
{
lean_object* v_tgt_1596_; lean_object* v_b_1597_; uint16_t v_v_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1606_; 
v_tgt_1596_ = lean_ctor_get(v_x_1434_, 0);
v_b_1597_ = lean_ctor_get(v_x_1434_, 1);
v_v_1598_ = lean_ctor_get_uint16(v_x_1434_, sizeof(void*)*2);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1600_ = v_x_1434_;
v_isShared_1601_ = v_isSharedCheck_1606_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_b_1597_);
lean_inc(v_tgt_1596_);
lean_dec(v_x_1434_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1606_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1602_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1597_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 1, v___x_1602_);
v___x_1604_ = v___x_1600_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(12, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_tgt_1596_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v___x_1602_);
lean_ctor_set_uint16(v_reuseFailAlloc_1605_, sizeof(void*)*2, v_v_1598_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
case 13:
{
lean_object* v_tgt_1607_; lean_object* v_b_1608_; uint32_t v_v_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1617_; 
v_tgt_1607_ = lean_ctor_get(v_x_1434_, 0);
v_b_1608_ = lean_ctor_get(v_x_1434_, 1);
v_v_1609_ = lean_ctor_get_uint32(v_x_1434_, sizeof(void*)*2);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1611_ = v_x_1434_;
v_isShared_1612_ = v_isSharedCheck_1617_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_b_1608_);
lean_inc(v_tgt_1607_);
lean_dec(v_x_1434_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1617_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; lean_object* v___x_1615_; 
v___x_1613_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1608_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 1, v___x_1613_);
v___x_1615_ = v___x_1611_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(13, 2, 4);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_tgt_1607_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v___x_1613_);
lean_ctor_set_uint32(v_reuseFailAlloc_1616_, sizeof(void*)*2, v_v_1609_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
case 14:
{
lean_object* v_tgt_1618_; lean_object* v_b_1619_; uint64_t v_v_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1628_; 
v_tgt_1618_ = lean_ctor_get(v_x_1434_, 0);
v_b_1619_ = lean_ctor_get(v_x_1434_, 1);
v_v_1620_ = lean_ctor_get_uint64(v_x_1434_, sizeof(void*)*2);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1622_ = v_x_1434_;
v_isShared_1623_ = v_isSharedCheck_1628_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_b_1619_);
lean_inc(v_tgt_1618_);
lean_dec(v_x_1434_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1628_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1624_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1619_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 1, v___x_1624_);
v___x_1626_ = v___x_1622_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(14, 2, 8);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_tgt_1618_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v___x_1624_);
lean_ctor_set_uint64(v_reuseFailAlloc_1627_, sizeof(void*)*2, v_v_1620_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
case 15:
{
lean_object* v_tgt_1629_; lean_object* v_b_1630_; uint64_t v_v_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1639_; 
v_tgt_1629_ = lean_ctor_get(v_x_1434_, 0);
v_b_1630_ = lean_ctor_get(v_x_1434_, 1);
v_v_1631_ = lean_ctor_get_uint64(v_x_1434_, sizeof(void*)*2);
v_isSharedCheck_1639_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1633_ = v_x_1434_;
v_isShared_1634_ = v_isSharedCheck_1639_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_b_1630_);
lean_inc(v_tgt_1629_);
lean_dec(v_x_1434_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1639_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; lean_object* v___x_1637_; 
v___x_1635_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1630_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 1, v___x_1635_);
v___x_1637_ = v___x_1633_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(15, 2, 8);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_tgt_1629_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v___x_1635_);
lean_ctor_set_uint64(v_reuseFailAlloc_1638_, sizeof(void*)*2, v_v_1631_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
case 16:
{
lean_object* v_tgt_1640_; lean_object* v_b_1641_; lean_object* v_v_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1650_; 
v_tgt_1640_ = lean_ctor_get(v_x_1434_, 0);
v_b_1641_ = lean_ctor_get(v_x_1434_, 1);
v_v_1642_ = lean_ctor_get(v_x_1434_, 2);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1644_ = v_x_1434_;
v_isShared_1645_ = v_isSharedCheck_1650_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_v_1642_);
lean_inc(v_b_1641_);
lean_inc(v_tgt_1640_);
lean_dec(v_x_1434_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1650_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1646_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1641_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 1, v___x_1646_);
v___x_1648_ = v___x_1644_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_tgt_1640_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v___x_1646_);
lean_ctor_set(v_reuseFailAlloc_1649_, 2, v_v_1642_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
case 17:
{
lean_object* v_tgt_1651_; lean_object* v_b_1652_; lean_object* v_v_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1661_; 
v_tgt_1651_ = lean_ctor_get(v_x_1434_, 0);
v_b_1652_ = lean_ctor_get(v_x_1434_, 1);
v_v_1653_ = lean_ctor_get(v_x_1434_, 2);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1655_ = v_x_1434_;
v_isShared_1656_ = v_isSharedCheck_1661_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_v_1653_);
lean_inc(v_b_1652_);
lean_inc(v_tgt_1651_);
lean_dec(v_x_1434_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1661_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1657_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1652_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 1, v___x_1657_);
v___x_1659_ = v___x_1655_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(17, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_tgt_1651_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_v_1653_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
case 18:
{
lean_object* v_tgt_1662_; lean_object* v_b_1663_; lean_object* v_x_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1673_; 
v_tgt_1662_ = lean_ctor_get(v_x_1434_, 0);
v_b_1663_ = lean_ctor_get(v_x_1434_, 1);
v_x_1664_ = lean_ctor_get(v_x_1434_, 2);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1666_ = v_x_1434_;
v_isShared_1667_ = v_isSharedCheck_1673_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_x_1664_);
lean_inc(v_b_1663_);
lean_inc(v_tgt_1662_);
lean_dec(v_x_1434_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1673_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
lean_inc_ref(v_f_1433_);
v___x_1668_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1663_);
v___x_1669_ = lean_apply_1(v_f_1433_, v_x_1664_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 2, v___x_1669_);
lean_ctor_set(v___x_1666_, 1, v___x_1668_);
v___x_1671_ = v___x_1666_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(18, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_tgt_1662_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1672_, 2, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
case 19:
{
lean_object* v_j_1674_; lean_object* v_xs_1675_; lean_object* v_v_1676_; lean_object* v_b_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1686_; 
v_j_1674_ = lean_ctor_get(v_x_1434_, 0);
v_xs_1675_ = lean_ctor_get(v_x_1434_, 1);
v_v_1676_ = lean_ctor_get(v_x_1434_, 2);
v_b_1677_ = lean_ctor_get(v_x_1434_, 3);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1679_ = v_x_1434_;
v_isShared_1680_ = v_isSharedCheck_1686_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_b_1677_);
lean_inc(v_v_1676_);
lean_inc(v_xs_1675_);
lean_inc(v_j_1674_);
lean_dec(v_x_1434_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1686_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1684_; 
lean_inc_ref(v_f_1433_);
v___x_1681_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_v_1676_);
v___x_1682_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1677_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 3, v___x_1682_);
lean_ctor_set(v___x_1679_, 2, v___x_1681_);
v___x_1684_ = v___x_1679_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(19, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_j_1674_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_xs_1675_);
lean_ctor_set(v_reuseFailAlloc_1685_, 2, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1685_, 3, v___x_1682_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
case 20:
{
lean_object* v_x_1687_; lean_object* v_i_1688_; lean_object* v_y_1689_; lean_object* v_b_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1710_; 
v_x_1687_ = lean_ctor_get(v_x_1434_, 0);
v_i_1688_ = lean_ctor_get(v_x_1434_, 1);
v_y_1689_ = lean_ctor_get(v_x_1434_, 2);
v_b_1690_ = lean_ctor_get(v_x_1434_, 3);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1692_ = v_x_1434_;
v_isShared_1693_ = v_isSharedCheck_1710_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_b_1690_);
lean_inc(v_y_1689_);
lean_inc(v_i_1688_);
lean_inc(v_x_1687_);
lean_dec(v_x_1434_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1710_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; lean_object* v___y_1696_; 
lean_inc_ref(v_f_1433_);
v___x_1694_ = lean_apply_1(v_f_1433_, v_x_1687_);
if (lean_obj_tag(v_y_1689_) == 0)
{
lean_object* v_id_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1709_; 
v_id_1701_ = lean_ctor_get(v_y_1689_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_y_1689_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1703_ = v_y_1689_;
v_isShared_1704_ = v_isSharedCheck_1709_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_id_1701_);
lean_dec(v_y_1689_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1709_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v___x_1707_; 
lean_inc_ref(v_f_1433_);
v___x_1705_ = lean_apply_1(v_f_1433_, v_id_1701_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1705_);
v___x_1707_ = v___x_1703_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
v___y_1696_ = v___x_1707_;
goto v___jp_1695_;
}
}
}
else
{
v___y_1696_ = v_y_1689_;
goto v___jp_1695_;
}
v___jp_1695_:
{
lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1697_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1690_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 3, v___x_1697_);
lean_ctor_set(v___x_1692_, 2, v___y_1696_);
lean_ctor_set(v___x_1692_, 0, v___x_1694_);
v___x_1699_ = v___x_1692_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(20, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1694_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_i_1688_);
lean_ctor_set(v_reuseFailAlloc_1700_, 2, v___y_1696_);
lean_ctor_set(v_reuseFailAlloc_1700_, 3, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
case 21:
{
lean_object* v_x_1711_; lean_object* v_cidx_1712_; lean_object* v_b_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1722_; 
v_x_1711_ = lean_ctor_get(v_x_1434_, 0);
v_cidx_1712_ = lean_ctor_get(v_x_1434_, 1);
v_b_1713_ = lean_ctor_get(v_x_1434_, 2);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1715_ = v_x_1434_;
v_isShared_1716_ = v_isSharedCheck_1722_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_b_1713_);
lean_inc(v_cidx_1712_);
lean_inc(v_x_1711_);
lean_dec(v_x_1434_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1722_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1720_; 
lean_inc_ref(v_f_1433_);
v___x_1717_ = lean_apply_1(v_f_1433_, v_x_1711_);
v___x_1718_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1713_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 2, v___x_1718_);
lean_ctor_set(v___x_1715_, 0, v___x_1717_);
v___x_1720_ = v___x_1715_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(21, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_cidx_1712_);
lean_ctor_set(v_reuseFailAlloc_1721_, 2, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
case 22:
{
lean_object* v_x_1723_; lean_object* v_i_1724_; lean_object* v_y_1725_; lean_object* v_b_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1736_; 
v_x_1723_ = lean_ctor_get(v_x_1434_, 0);
v_i_1724_ = lean_ctor_get(v_x_1434_, 1);
v_y_1725_ = lean_ctor_get(v_x_1434_, 2);
v_b_1726_ = lean_ctor_get(v_x_1434_, 3);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1728_ = v_x_1434_;
v_isShared_1729_ = v_isSharedCheck_1736_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_b_1726_);
lean_inc(v_y_1725_);
lean_inc(v_i_1724_);
lean_inc(v_x_1723_);
lean_dec(v_x_1434_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1736_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1734_; 
lean_inc_ref_n(v_f_1433_, 2);
v___x_1730_ = lean_apply_1(v_f_1433_, v_x_1723_);
v___x_1731_ = lean_apply_1(v_f_1433_, v_y_1725_);
v___x_1732_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1726_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 3, v___x_1732_);
lean_ctor_set(v___x_1728_, 2, v___x_1731_);
lean_ctor_set(v___x_1728_, 0, v___x_1730_);
v___x_1734_ = v___x_1728_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(22, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1730_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_i_1724_);
lean_ctor_set(v_reuseFailAlloc_1735_, 2, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1735_, 3, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
case 23:
{
lean_object* v_x_1737_; lean_object* v_i_1738_; lean_object* v_offset_1739_; lean_object* v_y_1740_; lean_object* v_ty_1741_; lean_object* v_b_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1752_; 
v_x_1737_ = lean_ctor_get(v_x_1434_, 0);
v_i_1738_ = lean_ctor_get(v_x_1434_, 1);
v_offset_1739_ = lean_ctor_get(v_x_1434_, 2);
v_y_1740_ = lean_ctor_get(v_x_1434_, 3);
v_ty_1741_ = lean_ctor_get(v_x_1434_, 4);
v_b_1742_ = lean_ctor_get(v_x_1434_, 5);
v_isSharedCheck_1752_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1744_ = v_x_1434_;
v_isShared_1745_ = v_isSharedCheck_1752_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_b_1742_);
lean_inc(v_ty_1741_);
lean_inc(v_y_1740_);
lean_inc(v_offset_1739_);
lean_inc(v_i_1738_);
lean_inc(v_x_1737_);
lean_dec(v_x_1434_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1752_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1750_; 
lean_inc_ref_n(v_f_1433_, 2);
v___x_1746_ = lean_apply_1(v_f_1433_, v_x_1737_);
v___x_1747_ = lean_apply_1(v_f_1433_, v_y_1740_);
v___x_1748_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1742_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 5, v___x_1748_);
lean_ctor_set(v___x_1744_, 3, v___x_1747_);
lean_ctor_set(v___x_1744_, 0, v___x_1746_);
v___x_1750_ = v___x_1744_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(23, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1746_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_i_1738_);
lean_ctor_set(v_reuseFailAlloc_1751_, 2, v_offset_1739_);
lean_ctor_set(v_reuseFailAlloc_1751_, 3, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1751_, 4, v_ty_1741_);
lean_ctor_set(v_reuseFailAlloc_1751_, 5, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
case 24:
{
lean_object* v_x_1753_; lean_object* v_n_1754_; uint8_t v_c_1755_; uint8_t v_persistent_1756_; lean_object* v_b_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1766_; 
v_x_1753_ = lean_ctor_get(v_x_1434_, 0);
v_n_1754_ = lean_ctor_get(v_x_1434_, 1);
v_c_1755_ = lean_ctor_get_uint8(v_x_1434_, sizeof(void*)*3);
v_persistent_1756_ = lean_ctor_get_uint8(v_x_1434_, sizeof(void*)*3 + 1);
v_b_1757_ = lean_ctor_get(v_x_1434_, 2);
v_isSharedCheck_1766_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1759_ = v_x_1434_;
v_isShared_1760_ = v_isSharedCheck_1766_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_b_1757_);
lean_inc(v_n_1754_);
lean_inc(v_x_1753_);
lean_dec(v_x_1434_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1766_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
lean_inc_ref(v_f_1433_);
v___x_1761_ = lean_apply_1(v_f_1433_, v_x_1753_);
v___x_1762_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1757_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 2, v___x_1762_);
lean_ctor_set(v___x_1759_, 0, v___x_1761_);
v___x_1764_ = v___x_1759_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(24, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v_n_1754_);
lean_ctor_set(v_reuseFailAlloc_1765_, 2, v___x_1762_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, sizeof(void*)*3, v_c_1755_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, sizeof(void*)*3 + 1, v_persistent_1756_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
case 25:
{
lean_object* v_x_1767_; lean_object* v_n_1768_; uint8_t v_c_1769_; uint8_t v_persistent_1770_; lean_object* v_b_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1780_; 
v_x_1767_ = lean_ctor_get(v_x_1434_, 0);
v_n_1768_ = lean_ctor_get(v_x_1434_, 1);
v_c_1769_ = lean_ctor_get_uint8(v_x_1434_, sizeof(void*)*3);
v_persistent_1770_ = lean_ctor_get_uint8(v_x_1434_, sizeof(void*)*3 + 1);
v_b_1771_ = lean_ctor_get(v_x_1434_, 2);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1773_ = v_x_1434_;
v_isShared_1774_ = v_isSharedCheck_1780_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_b_1771_);
lean_inc(v_n_1768_);
lean_inc(v_x_1767_);
lean_dec(v_x_1434_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1780_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1778_; 
lean_inc_ref(v_f_1433_);
v___x_1775_ = lean_apply_1(v_f_1433_, v_x_1767_);
v___x_1776_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1771_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 2, v___x_1776_);
lean_ctor_set(v___x_1773_, 0, v___x_1775_);
v___x_1778_ = v___x_1773_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(25, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_n_1768_);
lean_ctor_set(v_reuseFailAlloc_1779_, 2, v___x_1776_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*3, v_c_1769_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*3 + 1, v_persistent_1770_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
case 26:
{
lean_object* v_x_1781_; lean_object* v_b_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1791_; 
v_x_1781_ = lean_ctor_get(v_x_1434_, 0);
v_b_1782_ = lean_ctor_get(v_x_1434_, 1);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1784_ = v_x_1434_;
v_isShared_1785_ = v_isSharedCheck_1791_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_b_1782_);
lean_inc(v_x_1781_);
lean_dec(v_x_1434_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1791_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1789_; 
lean_inc_ref(v_f_1433_);
v___x_1786_ = lean_apply_1(v_f_1433_, v_x_1781_);
v___x_1787_ = l_Lean_IR_MapVars_mapFnBody(v_f_1433_, v_b_1782_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 1, v___x_1787_);
lean_ctor_set(v___x_1784_, 0, v___x_1786_);
v___x_1789_ = v___x_1784_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(26, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1786_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
case 27:
{
lean_object* v_tid_1792_; lean_object* v_x_1793_; lean_object* v_xType_1794_; lean_object* v_cs_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1806_; 
v_tid_1792_ = lean_ctor_get(v_x_1434_, 0);
v_x_1793_ = lean_ctor_get(v_x_1434_, 1);
v_xType_1794_ = lean_ctor_get(v_x_1434_, 2);
v_cs_1795_ = lean_ctor_get(v_x_1434_, 3);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1797_ = v_x_1434_;
v_isShared_1798_ = v_isSharedCheck_1806_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_cs_1795_);
lean_inc(v_xType_1794_);
lean_inc(v_x_1793_);
lean_inc(v_tid_1792_);
lean_dec(v_x_1434_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1806_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; size_t v_sz_1800_; size_t v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1804_; 
lean_inc_ref(v_f_1433_);
v___x_1799_ = lean_apply_1(v_f_1433_, v_x_1793_);
v_sz_1800_ = lean_array_size(v_cs_1795_);
v___x_1801_ = ((size_t)0ULL);
v___x_1802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(v_f_1433_, v_sz_1800_, v___x_1801_, v_cs_1795_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 3, v___x_1802_);
lean_ctor_set(v___x_1797_, 1, v___x_1799_);
v___x_1804_ = v___x_1797_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(27, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_tid_1792_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v___x_1799_);
lean_ctor_set(v_reuseFailAlloc_1805_, 2, v_xType_1794_);
lean_ctor_set(v_reuseFailAlloc_1805_, 3, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
case 28:
{
lean_object* v_x_1807_; 
v_x_1807_ = lean_ctor_get(v_x_1434_, 0);
lean_inc(v_x_1807_);
if (lean_obj_tag(v_x_1807_) == 0)
{
lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1823_; 
v_isSharedCheck_1823_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; 
v_unused_1824_ = lean_ctor_get(v_x_1434_, 0);
lean_dec(v_unused_1824_);
v___x_1809_ = v_x_1434_;
v_isShared_1810_ = v_isSharedCheck_1823_;
goto v_resetjp_1808_;
}
else
{
lean_dec(v_x_1434_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1823_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v_id_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1822_; 
v_id_1811_ = lean_ctor_get(v_x_1807_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_x_1807_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1813_ = v_x_1807_;
v_isShared_1814_ = v_isSharedCheck_1822_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_id_1811_);
lean_dec(v_x_1807_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1822_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1815_ = lean_apply_1(v_f_1433_, v_id_1811_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1815_);
v___x_1817_ = v___x_1813_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1819_; 
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1817_);
v___x_1819_ = v___x_1809_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(28, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_1433_);
return v_x_1434_;
}
}
case 29:
{
lean_object* v_j_1825_; lean_object* v_ys_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1834_; 
v_j_1825_ = lean_ctor_get(v_x_1434_, 0);
v_ys_1826_ = lean_ctor_get(v_x_1434_, 1);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1828_ = v_x_1434_;
v_isShared_1829_ = v_isSharedCheck_1834_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_ys_1826_);
lean_inc(v_j_1825_);
lean_dec(v_x_1434_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1834_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v___x_1832_; 
v___x_1830_ = l_Lean_IR_MapVars_mapArgs(v_f_1433_, v_ys_1826_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 1, v___x_1830_);
v___x_1832_ = v___x_1828_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(29, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_j_1825_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v___x_1830_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
default: 
{
lean_dec_ref(v_f_1433_);
return v_x_1434_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(lean_object* v_f_1835_, size_t v_sz_1836_, size_t v_i_1837_, lean_object* v_bs_1838_){
_start:
{
uint8_t v___x_1839_; 
v___x_1839_ = lean_usize_dec_lt(v_i_1837_, v_sz_1836_);
if (v___x_1839_ == 0)
{
lean_dec_ref(v_f_1835_);
return v_bs_1838_;
}
else
{
lean_object* v_v_1840_; lean_object* v___x_1841_; lean_object* v_bs_x27_1842_; lean_object* v___y_1844_; 
v_v_1840_ = lean_array_uget(v_bs_1838_, v_i_1837_);
v___x_1841_ = lean_unsigned_to_nat(0u);
v_bs_x27_1842_ = lean_array_uset(v_bs_1838_, v_i_1837_, v___x_1841_);
if (lean_obj_tag(v_v_1840_) == 0)
{
lean_object* v_info_1849_; lean_object* v_b_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1858_; 
v_info_1849_ = lean_ctor_get(v_v_1840_, 0);
v_b_1850_ = lean_ctor_get(v_v_1840_, 1);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_v_1840_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1852_ = v_v_1840_;
v_isShared_1853_ = v_isSharedCheck_1858_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_b_1850_);
lean_inc(v_info_1849_);
lean_dec(v_v_1840_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1858_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
lean_inc_ref(v_f_1835_);
v___x_1854_ = l_Lean_IR_MapVars_mapFnBody(v_f_1835_, v_b_1850_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 1, v___x_1854_);
v___x_1856_ = v___x_1852_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_info_1849_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
v___y_1844_ = v___x_1856_;
goto v___jp_1843_;
}
}
}
else
{
lean_object* v_b_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1867_; 
v_b_1859_ = lean_ctor_get(v_v_1840_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_v_1840_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1861_ = v_v_1840_;
v_isShared_1862_ = v_isSharedCheck_1867_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_b_1859_);
lean_dec(v_v_1840_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1867_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1865_; 
lean_inc_ref(v_f_1835_);
v___x_1863_ = l_Lean_IR_MapVars_mapFnBody(v_f_1835_, v_b_1859_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1863_);
v___x_1865_ = v___x_1861_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
v___y_1844_ = v___x_1865_;
goto v___jp_1843_;
}
}
}
v___jp_1843_:
{
size_t v___x_1845_; size_t v___x_1846_; lean_object* v___x_1847_; 
v___x_1845_ = ((size_t)1ULL);
v___x_1846_ = lean_usize_add(v_i_1837_, v___x_1845_);
v___x_1847_ = lean_array_uset(v_bs_x27_1842_, v_i_1837_, v___y_1844_);
v_i_1837_ = v___x_1846_;
v_bs_1838_ = v___x_1847_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0___boxed(lean_object* v_f_1868_, lean_object* v_sz_1869_, lean_object* v_i_1870_, lean_object* v_bs_1871_){
_start:
{
size_t v_sz_boxed_1872_; size_t v_i_boxed_1873_; lean_object* v_res_1874_; 
v_sz_boxed_1872_ = lean_unbox_usize(v_sz_1869_);
lean_dec(v_sz_1869_);
v_i_boxed_1873_ = lean_unbox_usize(v_i_1870_);
lean_dec(v_i_1870_);
v_res_1874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(v_f_1868_, v_sz_boxed_1872_, v_i_boxed_1873_, v_bs_1871_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_mapVars(lean_object* v_f_1875_, lean_object* v_b_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Lean_IR_MapVars_mapFnBody(v_f_1875_, v_b_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lam__0(lean_object* v_x_1878_, lean_object* v_y_1879_, lean_object* v_z_1880_){
_start:
{
uint8_t v___x_1881_; 
v___x_1881_ = l_Lean_IR_instBEqVarId_beq(v_x_1878_, v_z_1880_);
if (v___x_1881_ == 0)
{
lean_inc(v_z_1880_);
return v_z_1880_;
}
else
{
lean_inc(v_y_1879_);
return v_y_1879_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lam__0___boxed(lean_object* v_x_1882_, lean_object* v_y_1883_, lean_object* v_z_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_IR_FnBody_replaceVar___lam__0(v_x_1882_, v_y_1883_, v_z_1884_);
lean_dec(v_z_1884_);
lean_dec(v_y_1883_);
lean_dec(v_x_1882_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar(lean_object* v_x_1886_, lean_object* v_y_1887_, lean_object* v_b_1888_){
_start:
{
lean_object* v___f_1889_; lean_object* v___x_1890_; 
v___f_1889_ = lean_alloc_closure((void*)(l_Lean_IR_FnBody_replaceVar___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1889_, 0, v_x_1886_);
lean_closure_set(v___f_1889_, 1, v_y_1887_);
v___x_1890_ = l_Lean_IR_MapVars_mapFnBody(v___f_1889_, v_b_1888_);
return v___x_1890_;
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
