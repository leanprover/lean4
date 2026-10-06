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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
v___x_343_ = lean_unbox(v_fst_342_);
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
v___x_383_ = lean_unbox(v_fst_382_);
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
case 19:
{
lean_object* v_j_406_; lean_object* v_xs_407_; lean_object* v_b_408_; lean_object* v___x_409_; lean_object* v_fst_410_; uint8_t v___x_411_; 
v_j_406_ = lean_ctor_get(v_x_399_, 0);
lean_inc(v_j_406_);
v_xs_407_ = lean_ctor_get(v_x_399_, 1);
lean_inc_ref(v_xs_407_);
v_b_408_ = lean_ctor_get(v_x_399_, 3);
lean_inc(v_b_408_);
lean_dec_ref_known(v_x_399_, 4);
v___x_409_ = l_Lean_IR_UniqueIds_checkId(v_j_406_, v_a_400_);
v_fst_410_ = lean_ctor_get(v___x_409_, 0);
v___x_411_ = lean_unbox(v_fst_410_);
if (v___x_411_ == 0)
{
lean_dec(v_b_408_);
lean_dec_ref(v_xs_407_);
return v___x_409_;
}
else
{
lean_object* v_snd_412_; lean_object* v___x_413_; lean_object* v_fst_414_; uint8_t v___x_415_; 
v_snd_412_ = lean_ctor_get(v___x_409_, 1);
lean_inc(v_snd_412_);
lean_dec_ref(v___x_409_);
v___x_413_ = l_Lean_IR_UniqueIds_checkParams(v_xs_407_, v_snd_412_);
lean_dec_ref(v_xs_407_);
v_fst_414_ = lean_ctor_get(v___x_413_, 0);
v___x_415_ = lean_unbox(v_fst_414_);
if (v___x_415_ == 0)
{
lean_dec(v_b_408_);
return v___x_413_;
}
else
{
lean_object* v_snd_416_; 
v_snd_416_ = lean_ctor_get(v___x_413_, 1);
lean_inc(v_snd_416_);
lean_dec_ref(v___x_413_);
v_x_399_ = v_b_408_;
v_a_400_ = v_snd_416_;
goto _start;
}
}
}
case 27:
{
lean_object* v_cs_418_; lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v_cs_418_ = lean_ctor_get(v_x_399_, 3);
lean_inc_ref(v_cs_418_);
lean_dec_ref_known(v_x_399_, 4);
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = lean_array_get_size(v_cs_418_);
v___x_421_ = lean_nat_dec_lt(v___x_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_dec_ref(v_cs_418_);
v___y_402_ = v_a_400_;
goto v___jp_401_;
}
else
{
if (v___x_421_ == 0)
{
lean_dec_ref(v_cs_418_);
v___y_402_ = v_a_400_;
goto v___jp_401_;
}
else
{
size_t v___x_422_; size_t v___x_423_; lean_object* v___x_424_; lean_object* v_fst_425_; uint8_t v___x_426_; 
v___x_422_ = ((size_t)0ULL);
v___x_423_ = lean_usize_of_nat(v___x_420_);
v___x_424_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(v_cs_418_, v___x_422_, v___x_423_, v_a_400_);
lean_dec_ref(v_cs_418_);
v_fst_425_ = lean_ctor_get(v___x_424_, 0);
v___x_426_ = lean_unbox(v_fst_425_);
if (v___x_426_ == 0)
{
lean_object* v_snd_427_; 
v_snd_427_ = lean_ctor_get(v___x_424_, 1);
lean_inc(v_snd_427_);
lean_dec_ref(v___x_424_);
v___y_402_ = v_snd_427_;
goto v___jp_401_;
}
else
{
lean_object* v_snd_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_437_; 
v_snd_428_ = lean_ctor_get(v___x_424_, 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; 
v_unused_438_ = lean_ctor_get(v___x_424_, 0);
lean_dec(v_unused_438_);
v___x_430_ = v___x_424_;
v_isShared_431_ = v_isSharedCheck_437_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_snd_428_);
lean_dec(v___x_424_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_437_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
uint8_t v___x_432_; lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_432_ = 0;
v___x_433_ = lean_box(v___x_432_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_433_);
v___x_435_ = v___x_430_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_snd_428_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
}
default: 
{
uint8_t v___x_439_; 
v___x_439_ = l_Lean_IR_FnBody_isVarDecl(v_x_399_);
if (v___x_439_ == 0)
{
uint8_t v___x_440_; 
v___x_440_ = l_Lean_IR_FnBody_isTerminal(v_x_399_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_IR_FnBody_body(v_x_399_);
lean_dec(v_x_399_);
v_x_399_ = v___x_441_;
goto _start;
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec(v_x_399_);
v___x_443_ = lean_box(v___x_440_);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v_a_400_);
return v___x_444_;
}
}
else
{
lean_object* v_x_445_; lean_object* v___x_446_; lean_object* v_fst_447_; uint8_t v___x_448_; 
v_x_445_ = l_Lean_IR_FnBody_targetVar(v_x_399_);
v___x_446_ = l_Lean_IR_UniqueIds_checkId(v_x_445_, v_a_400_);
v_fst_447_ = lean_ctor_get(v___x_446_, 0);
v___x_448_ = lean_unbox(v_fst_447_);
if (v___x_448_ == 0)
{
lean_dec(v_x_399_);
return v___x_446_;
}
else
{
lean_object* v_snd_449_; lean_object* v_b_450_; 
v_snd_449_ = lean_ctor_get(v___x_446_, 1);
lean_inc(v_snd_449_);
lean_dec_ref(v___x_446_);
v_b_450_ = l_Lean_IR_FnBody_body(v_x_399_);
lean_dec(v_x_399_);
v_x_399_ = v_b_450_;
v_a_400_ = v_snd_449_;
goto _start;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(lean_object* v_as_452_, size_t v_i_453_, size_t v_stop_454_, lean_object* v___y_455_){
_start:
{
uint8_t v___x_456_; 
v___x_456_ = lean_usize_dec_eq(v_i_453_, v_stop_454_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v_fst_460_; uint8_t v___x_461_; 
v___x_457_ = lean_array_uget_borrowed(v_as_452_, v_i_453_);
v___x_458_ = l_Lean_IR_Alt_body(v___x_457_);
v___x_459_ = l_Lean_IR_UniqueIds_checkFnBody(v___x_458_, v___y_455_);
v_fst_460_ = lean_ctor_get(v___x_459_, 0);
v___x_461_ = lean_unbox(v_fst_460_);
if (v___x_461_ == 0)
{
lean_object* v_snd_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_471_; 
v_snd_462_ = lean_ctor_get(v___x_459_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_471_ == 0)
{
lean_object* v_unused_472_; 
v_unused_472_ = lean_ctor_get(v___x_459_, 0);
lean_dec(v_unused_472_);
v___x_464_ = v___x_459_;
v_isShared_465_ = v_isSharedCheck_471_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_snd_462_);
lean_dec(v___x_459_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_471_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
uint8_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_466_ = 1;
v___x_467_ = lean_box(v___x_466_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_467_);
v___x_469_ = v___x_464_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_snd_462_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
else
{
lean_object* v_snd_473_; size_t v___x_474_; size_t v___x_475_; 
v_snd_473_ = lean_ctor_get(v___x_459_, 1);
lean_inc(v_snd_473_);
lean_dec_ref(v___x_459_);
v___x_474_ = ((size_t)1ULL);
v___x_475_ = lean_usize_add(v_i_453_, v___x_474_);
v_i_453_ = v___x_475_;
v___y_455_ = v_snd_473_;
goto _start;
}
}
else
{
uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = 0;
v___x_478_ = lean_box(v___x_477_);
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v___y_455_);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0___boxed(lean_object* v_as_480_, lean_object* v_i_481_, lean_object* v_stop_482_, lean_object* v___y_483_){
_start:
{
size_t v_i_boxed_484_; size_t v_stop_boxed_485_; lean_object* v_res_486_; 
v_i_boxed_484_ = lean_unbox_usize(v_i_481_);
lean_dec(v_i_481_);
v_stop_boxed_485_ = lean_unbox_usize(v_stop_482_);
lean_dec(v_stop_482_);
v_res_486_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_UniqueIds_checkFnBody_spec__0(v_as_480_, v_i_boxed_484_, v_stop_boxed_485_, v___y_483_);
lean_dec_ref(v_as_480_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkDecl(lean_object* v_x_487_, lean_object* v_a_488_){
_start:
{
if (lean_obj_tag(v_x_487_) == 0)
{
lean_object* v_xs_489_; lean_object* v_body_490_; lean_object* v___x_491_; lean_object* v_fst_492_; uint8_t v___x_493_; 
v_xs_489_ = lean_ctor_get(v_x_487_, 1);
lean_inc_ref(v_xs_489_);
v_body_490_ = lean_ctor_get(v_x_487_, 3);
lean_inc(v_body_490_);
lean_dec_ref_known(v_x_487_, 5);
v___x_491_ = l_Lean_IR_UniqueIds_checkParams(v_xs_489_, v_a_488_);
lean_dec_ref(v_xs_489_);
v_fst_492_ = lean_ctor_get(v___x_491_, 0);
v___x_493_ = lean_unbox(v_fst_492_);
if (v___x_493_ == 0)
{
lean_dec(v_body_490_);
return v___x_491_;
}
else
{
lean_object* v_snd_494_; lean_object* v___x_495_; 
v_snd_494_ = lean_ctor_get(v___x_491_, 1);
lean_inc(v_snd_494_);
lean_dec_ref(v___x_491_);
v___x_495_ = l_Lean_IR_UniqueIds_checkFnBody(v_body_490_, v_snd_494_);
return v___x_495_;
}
}
else
{
lean_object* v_xs_496_; lean_object* v___x_497_; 
v_xs_496_ = lean_ctor_get(v_x_487_, 1);
lean_inc_ref(v_xs_496_);
lean_dec_ref_known(v_x_487_, 4);
v___x_497_ = l_Lean_IR_UniqueIds_checkParams(v_xs_496_, v_a_488_);
lean_dec_ref(v_xs_496_);
return v___x_497_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Decl_uniqueIds(lean_object* v_d_498_){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v_fst_501_; uint8_t v___x_502_; 
v___x_499_ = lean_box(1);
v___x_500_ = l_Lean_IR_UniqueIds_checkDecl(v_d_498_, v___x_499_);
v_fst_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_fst_501_);
lean_dec_ref(v___x_500_);
v___x_502_ = lean_unbox(v_fst_501_);
lean_dec(v_fst_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_uniqueIds___boxed(lean_object* v_d_503_){
_start:
{
uint8_t v_res_504_; lean_object* v_r_505_; 
v_res_504_ = l_Lean_IR_Decl_uniqueIds(v_d_503_);
v_r_505_ = lean_box(v_res_504_);
return v_r_505_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(lean_object* v_t_506_, lean_object* v_k_507_){
_start:
{
if (lean_obj_tag(v_t_506_) == 0)
{
lean_object* v_k_508_; lean_object* v_v_509_; lean_object* v_l_510_; lean_object* v_r_511_; uint8_t v___x_512_; 
v_k_508_ = lean_ctor_get(v_t_506_, 1);
v_v_509_ = lean_ctor_get(v_t_506_, 2);
v_l_510_ = lean_ctor_get(v_t_506_, 3);
v_r_511_ = lean_ctor_get(v_t_506_, 4);
v___x_512_ = lean_nat_dec_lt(v_k_507_, v_k_508_);
if (v___x_512_ == 0)
{
uint8_t v___x_513_; 
v___x_513_ = lean_nat_dec_eq(v_k_507_, v_k_508_);
if (v___x_513_ == 0)
{
v_t_506_ = v_r_511_;
goto _start;
}
else
{
lean_object* v___x_515_; 
lean_inc(v_v_509_);
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v_v_509_);
return v___x_515_;
}
}
else
{
v_t_506_ = v_l_510_;
goto _start;
}
}
else
{
lean_object* v___x_517_; 
v___x_517_ = lean_box(0);
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg___boxed(lean_object* v_t_518_, lean_object* v_k_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_t_518_, v_k_519_);
lean_dec(v_k_519_);
lean_dec(v_t_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normIndex(lean_object* v_x_521_, lean_object* v_m_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_m_522_, v_x_521_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_inc(v_x_521_);
return v_x_521_;
}
else
{
lean_object* v_val_524_; 
v_val_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_val_524_);
lean_dec_ref_known(v___x_523_, 1);
return v_val_524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normIndex___boxed(lean_object* v_x_525_, lean_object* v_m_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_IR_NormalizeIds_normIndex(v_x_525_, v_m_526_);
lean_dec(v_m_526_);
lean_dec(v_x_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0(lean_object* v_00_u03b4_528_, lean_object* v_t_529_, lean_object* v_k_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___redArg(v_t_529_, v_k_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0___boxed(lean_object* v_00_u03b4_532_, lean_object* v_t_533_, lean_object* v_k_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_NormalizeIds_normIndex_spec__0(v_00_u03b4_532_, v_t_533_, v_k_534_);
lean_dec(v_k_534_);
lean_dec(v_t_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normVar(lean_object* v_x_536_, lean_object* v_a_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_IR_NormalizeIds_normIndex(v_x_536_, v_a_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normVar___boxed(lean_object* v_x_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_IR_NormalizeIds_normVar(v_x_539_, v_a_540_);
lean_dec(v_a_540_);
lean_dec(v_x_539_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normJP(lean_object* v_x_542_, lean_object* v_a_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_IR_NormalizeIds_normIndex(v_x_542_, v_a_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normJP___boxed(lean_object* v_x_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_IR_NormalizeIds_normJP(v_x_545_, v_a_546_);
lean_dec(v_a_546_);
lean_dec(v_x_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArg(lean_object* v_x_548_, lean_object* v_a_549_){
_start:
{
if (lean_obj_tag(v_x_548_) == 0)
{
lean_object* v_id_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_558_; 
v_id_550_ = lean_ctor_get(v_x_548_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v_x_548_);
if (v_isSharedCheck_558_ == 0)
{
v___x_552_ = v_x_548_;
v_isShared_553_ = v_isSharedCheck_558_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_id_550_);
lean_dec(v_x_548_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_558_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = l_Lean_IR_NormalizeIds_normIndex(v_id_550_, v_a_549_);
lean_dec(v_id_550_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_554_);
v___x_556_ = v___x_552_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
else
{
return v_x_548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArg___boxed(lean_object* v_x_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_IR_NormalizeIds_normArg(v_x_559_, v_a_560_);
lean_dec(v_a_560_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(lean_object* v_m_562_, size_t v_sz_563_, size_t v_i_564_, lean_object* v_bs_565_){
_start:
{
uint8_t v___x_566_; 
v___x_566_ = lean_usize_dec_lt(v_i_564_, v_sz_563_);
if (v___x_566_ == 0)
{
return v_bs_565_;
}
else
{
lean_object* v_v_567_; lean_object* v___x_568_; lean_object* v_bs_x27_569_; lean_object* v___x_570_; size_t v___x_571_; size_t v___x_572_; lean_object* v___x_573_; 
v_v_567_ = lean_array_uget(v_bs_565_, v_i_564_);
v___x_568_ = lean_unsigned_to_nat(0u);
v_bs_x27_569_ = lean_array_uset(v_bs_565_, v_i_564_, v___x_568_);
v___x_570_ = l_Lean_IR_NormalizeIds_normArg(v_v_567_, v_m_562_);
v___x_571_ = ((size_t)1ULL);
v___x_572_ = lean_usize_add(v_i_564_, v___x_571_);
v___x_573_ = lean_array_uset(v_bs_x27_569_, v_i_564_, v___x_570_);
v_i_564_ = v___x_572_;
v_bs_565_ = v___x_573_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0___boxed(lean_object* v_m_575_, lean_object* v_sz_576_, lean_object* v_i_577_, lean_object* v_bs_578_){
_start:
{
size_t v_sz_boxed_579_; size_t v_i_boxed_580_; lean_object* v_res_581_; 
v_sz_boxed_579_ = lean_unbox_usize(v_sz_576_);
lean_dec(v_sz_576_);
v_i_boxed_580_ = lean_unbox_usize(v_i_577_);
lean_dec(v_i_577_);
v_res_581_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(v_m_575_, v_sz_boxed_579_, v_i_boxed_580_, v_bs_578_);
lean_dec(v_m_575_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArgs(lean_object* v_as_582_, lean_object* v_m_583_){
_start:
{
size_t v_sz_584_; size_t v___x_585_; lean_object* v___x_586_; 
v_sz_584_ = lean_array_size(v_as_582_);
v___x_585_ = ((size_t)0ULL);
v___x_586_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normArgs_spec__0(v_m_583_, v_sz_584_, v___x_585_, v_as_582_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArgs___boxed(lean_object* v_as_587_, lean_object* v_m_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_IR_NormalizeIds_normArgs(v_as_587_, v_m_588_);
lean_dec(v_m_588_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0(lean_object* v_msg_597_){
_start:
{
lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___f_600_; lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___f_603_; lean_object* v___f_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___f_598_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__0));
v___f_599_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__1));
v___f_600_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__2));
v___f_601_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__3));
v___f_602_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__4));
v___f_603_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__5));
v___f_604_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__6));
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___f_598_);
lean_ctor_set(v___x_605_, 1, v___f_599_);
v___x_606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v___f_600_);
lean_ctor_set(v___x_606_, 2, v___f_601_);
lean_ctor_set(v___x_606_, 3, v___f_602_);
lean_ctor_set(v___x_606_, 4, v___f_603_);
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v___f_604_);
v___x_608_ = l_Lean_IR_instInhabitedFnBody_default__1;
v___x_609_ = l_instInhabitedOfMonad___redArg(v___x_607_, v___x_608_);
v___x_610_ = lean_panic_fn_borrowed(v___x_609_, v_msg_597_);
lean_dec(v___x_609_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_IR_NormalizeIds_normExpr___closed__3(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_614_ = ((lean_object*)(l_Lean_IR_NormalizeIds_normExpr___closed__2));
v___x_615_ = lean_unsigned_to_nat(12u);
v___x_616_ = lean_unsigned_to_nat(87u);
v___x_617_ = ((lean_object*)(l_Lean_IR_NormalizeIds_normExpr___closed__1));
v___x_618_ = ((lean_object*)(l_Lean_IR_NormalizeIds_normExpr___closed__0));
v___x_619_ = l_mkPanicMessageWithDecl(v___x_618_, v___x_617_, v___x_616_, v___x_615_, v___x_614_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normExpr(lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
switch(lean_obj_tag(v_x_620_))
{
case 0:
{
lean_object* v_tgt_622_; lean_object* v_b_623_; lean_object* v_i_624_; lean_object* v_ys_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_633_; 
v_tgt_622_ = lean_ctor_get(v_x_620_, 0);
v_b_623_ = lean_ctor_get(v_x_620_, 1);
v_i_624_ = lean_ctor_get(v_x_620_, 2);
v_ys_625_ = lean_ctor_get(v_x_620_, 3);
v_isSharedCheck_633_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_633_ == 0)
{
v___x_627_ = v_x_620_;
v_isShared_628_ = v_isSharedCheck_633_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_ys_625_);
lean_inc(v_i_624_);
lean_inc(v_b_623_);
lean_inc(v_tgt_622_);
lean_dec(v_x_620_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_633_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_629_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_625_, v_x_621_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 3, v___x_629_);
v___x_631_ = v___x_627_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_tgt_622_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_b_623_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_i_624_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
case 1:
{
lean_object* v_tgt_634_; lean_object* v_b_635_; lean_object* v_n_636_; lean_object* v_x_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_645_; 
v_tgt_634_ = lean_ctor_get(v_x_620_, 0);
v_b_635_ = lean_ctor_get(v_x_620_, 1);
v_n_636_ = lean_ctor_get(v_x_620_, 2);
v_x_637_ = lean_ctor_get(v_x_620_, 3);
v_isSharedCheck_645_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_645_ == 0)
{
v___x_639_ = v_x_620_;
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_x_637_);
lean_inc(v_n_636_);
lean_inc(v_b_635_);
lean_inc(v_tgt_634_);
lean_dec(v_x_620_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_641_ = l_Lean_IR_NormalizeIds_normIndex(v_x_637_, v_x_621_);
lean_dec(v_x_637_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 3, v___x_641_);
v___x_643_ = v___x_639_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_tgt_634_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_b_635_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_n_636_);
lean_ctor_set(v_reuseFailAlloc_644_, 3, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
case 2:
{
lean_object* v_tgt_646_; lean_object* v_b_647_; lean_object* v_x_648_; lean_object* v_i_649_; uint8_t v_updtHeader_650_; lean_object* v_ys_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_660_; 
v_tgt_646_ = lean_ctor_get(v_x_620_, 0);
v_b_647_ = lean_ctor_get(v_x_620_, 1);
v_x_648_ = lean_ctor_get(v_x_620_, 2);
v_i_649_ = lean_ctor_get(v_x_620_, 3);
v_updtHeader_650_ = lean_ctor_get_uint8(v_x_620_, sizeof(void*)*5);
v_ys_651_ = lean_ctor_get(v_x_620_, 4);
v_isSharedCheck_660_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_660_ == 0)
{
v___x_653_ = v_x_620_;
v_isShared_654_ = v_isSharedCheck_660_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_ys_651_);
lean_inc(v_i_649_);
lean_inc(v_x_648_);
lean_inc(v_b_647_);
lean_inc(v_tgt_646_);
lean_dec(v_x_620_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_660_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_655_ = l_Lean_IR_NormalizeIds_normIndex(v_x_648_, v_x_621_);
lean_dec(v_x_648_);
v___x_656_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_651_, v_x_621_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 4, v___x_656_);
lean_ctor_set(v___x_653_, 2, v___x_655_);
v___x_658_ = v___x_653_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(2, 5, 1);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_tgt_646_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_b_647_);
lean_ctor_set(v_reuseFailAlloc_659_, 2, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_659_, 3, v_i_649_);
lean_ctor_set(v_reuseFailAlloc_659_, 4, v___x_656_);
lean_ctor_set_uint8(v_reuseFailAlloc_659_, sizeof(void*)*5, v_updtHeader_650_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
case 3:
{
lean_object* v_tgt_661_; lean_object* v_b_662_; lean_object* v_i_663_; lean_object* v_x_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_672_; 
v_tgt_661_ = lean_ctor_get(v_x_620_, 0);
v_b_662_ = lean_ctor_get(v_x_620_, 1);
v_i_663_ = lean_ctor_get(v_x_620_, 2);
v_x_664_ = lean_ctor_get(v_x_620_, 3);
v_isSharedCheck_672_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_672_ == 0)
{
v___x_666_ = v_x_620_;
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_x_664_);
lean_inc(v_i_663_);
lean_inc(v_b_662_);
lean_inc(v_tgt_661_);
lean_dec(v_x_620_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_668_ = l_Lean_IR_NormalizeIds_normIndex(v_x_664_, v_x_621_);
lean_dec(v_x_664_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 3, v___x_668_);
v___x_670_ = v___x_666_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_tgt_661_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_b_662_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v_i_663_);
lean_ctor_set(v_reuseFailAlloc_671_, 3, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
case 4:
{
lean_object* v_tgt_673_; lean_object* v_b_674_; lean_object* v_i_675_; lean_object* v_x_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_684_; 
v_tgt_673_ = lean_ctor_get(v_x_620_, 0);
v_b_674_ = lean_ctor_get(v_x_620_, 1);
v_i_675_ = lean_ctor_get(v_x_620_, 2);
v_x_676_ = lean_ctor_get(v_x_620_, 3);
v_isSharedCheck_684_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_684_ == 0)
{
v___x_678_ = v_x_620_;
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_x_676_);
lean_inc(v_i_675_);
lean_inc(v_b_674_);
lean_inc(v_tgt_673_);
lean_dec(v_x_620_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_680_ = l_Lean_IR_NormalizeIds_normIndex(v_x_676_, v_x_621_);
lean_dec(v_x_676_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 3, v___x_680_);
v___x_682_ = v___x_678_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_tgt_673_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_b_674_);
lean_ctor_set(v_reuseFailAlloc_683_, 2, v_i_675_);
lean_ctor_set(v_reuseFailAlloc_683_, 3, v___x_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
case 5:
{
lean_object* v_tgt_685_; lean_object* v_b_686_; lean_object* v_ty_687_; lean_object* v_n_688_; lean_object* v_offset_689_; lean_object* v_x_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_698_; 
v_tgt_685_ = lean_ctor_get(v_x_620_, 0);
v_b_686_ = lean_ctor_get(v_x_620_, 1);
v_ty_687_ = lean_ctor_get(v_x_620_, 2);
v_n_688_ = lean_ctor_get(v_x_620_, 3);
v_offset_689_ = lean_ctor_get(v_x_620_, 4);
v_x_690_ = lean_ctor_get(v_x_620_, 5);
v_isSharedCheck_698_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_698_ == 0)
{
v___x_692_ = v_x_620_;
v_isShared_693_ = v_isSharedCheck_698_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_x_690_);
lean_inc(v_offset_689_);
lean_inc(v_n_688_);
lean_inc(v_ty_687_);
lean_inc(v_b_686_);
lean_inc(v_tgt_685_);
lean_dec(v_x_620_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_698_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = l_Lean_IR_NormalizeIds_normIndex(v_x_690_, v_x_621_);
lean_dec(v_x_690_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 5, v___x_694_);
v___x_696_ = v___x_692_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_tgt_685_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_b_686_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v_ty_687_);
lean_ctor_set(v_reuseFailAlloc_697_, 3, v_n_688_);
lean_ctor_set(v_reuseFailAlloc_697_, 4, v_offset_689_);
lean_ctor_set(v_reuseFailAlloc_697_, 5, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
case 6:
{
lean_object* v_tgt_699_; lean_object* v_b_700_; lean_object* v_ty_701_; lean_object* v_c_702_; lean_object* v_ys_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_711_; 
v_tgt_699_ = lean_ctor_get(v_x_620_, 0);
v_b_700_ = lean_ctor_get(v_x_620_, 1);
v_ty_701_ = lean_ctor_get(v_x_620_, 2);
v_c_702_ = lean_ctor_get(v_x_620_, 3);
v_ys_703_ = lean_ctor_get(v_x_620_, 4);
v_isSharedCheck_711_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_711_ == 0)
{
v___x_705_ = v_x_620_;
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_ys_703_);
lean_inc(v_c_702_);
lean_inc(v_ty_701_);
lean_inc(v_b_700_);
lean_inc(v_tgt_699_);
lean_dec(v_x_620_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_707_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_703_, v_x_621_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 4, v___x_707_);
v___x_709_ = v___x_705_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(6, 5, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_tgt_699_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_b_700_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_ty_701_);
lean_ctor_set(v_reuseFailAlloc_710_, 3, v_c_702_);
lean_ctor_set(v_reuseFailAlloc_710_, 4, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
case 7:
{
lean_object* v_tgt_712_; lean_object* v_b_713_; lean_object* v_c_714_; lean_object* v_ys_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_723_; 
v_tgt_712_ = lean_ctor_get(v_x_620_, 0);
v_b_713_ = lean_ctor_get(v_x_620_, 1);
v_c_714_ = lean_ctor_get(v_x_620_, 2);
v_ys_715_ = lean_ctor_get(v_x_620_, 3);
v_isSharedCheck_723_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_723_ == 0)
{
v___x_717_ = v_x_620_;
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_ys_715_);
lean_inc(v_c_714_);
lean_inc(v_b_713_);
lean_inc(v_tgt_712_);
lean_dec(v_x_620_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_719_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_715_, v_x_621_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 3, v___x_719_);
v___x_721_ = v___x_717_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_tgt_712_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_b_713_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_c_714_);
lean_ctor_set(v_reuseFailAlloc_722_, 3, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
case 8:
{
lean_object* v_tgt_724_; lean_object* v_b_725_; lean_object* v_x_726_; lean_object* v_ys_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_736_; 
v_tgt_724_ = lean_ctor_get(v_x_620_, 0);
v_b_725_ = lean_ctor_get(v_x_620_, 1);
v_x_726_ = lean_ctor_get(v_x_620_, 2);
v_ys_727_ = lean_ctor_get(v_x_620_, 3);
v_isSharedCheck_736_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_736_ == 0)
{
v___x_729_ = v_x_620_;
v_isShared_730_ = v_isSharedCheck_736_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_ys_727_);
lean_inc(v_x_726_);
lean_inc(v_b_725_);
lean_inc(v_tgt_724_);
lean_dec(v_x_620_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_736_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_731_ = l_Lean_IR_NormalizeIds_normIndex(v_x_726_, v_x_621_);
lean_dec(v_x_726_);
v___x_732_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_727_, v_x_621_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 3, v___x_732_);
lean_ctor_set(v___x_729_, 2, v___x_731_);
v___x_734_ = v___x_729_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_tgt_724_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_b_725_);
lean_ctor_set(v_reuseFailAlloc_735_, 2, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_735_, 3, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
case 9:
{
lean_object* v_tgt_737_; lean_object* v_b_738_; lean_object* v_ty_739_; lean_object* v_x_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_748_; 
v_tgt_737_ = lean_ctor_get(v_x_620_, 0);
v_b_738_ = lean_ctor_get(v_x_620_, 1);
v_ty_739_ = lean_ctor_get(v_x_620_, 2);
v_x_740_ = lean_ctor_get(v_x_620_, 3);
v_isSharedCheck_748_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_748_ == 0)
{
v___x_742_ = v_x_620_;
v_isShared_743_ = v_isSharedCheck_748_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_x_740_);
lean_inc(v_ty_739_);
lean_inc(v_b_738_);
lean_inc(v_tgt_737_);
lean_dec(v_x_620_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_748_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_744_ = l_Lean_IR_NormalizeIds_normIndex(v_x_740_, v_x_621_);
lean_dec(v_x_740_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 3, v___x_744_);
v___x_746_ = v___x_742_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_tgt_737_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_b_738_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_ty_739_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
case 10:
{
lean_object* v_tgt_749_; lean_object* v_b_750_; lean_object* v_ty_751_; lean_object* v_x_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_760_; 
v_tgt_749_ = lean_ctor_get(v_x_620_, 0);
v_b_750_ = lean_ctor_get(v_x_620_, 1);
v_ty_751_ = lean_ctor_get(v_x_620_, 2);
v_x_752_ = lean_ctor_get(v_x_620_, 3);
v_isSharedCheck_760_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_760_ == 0)
{
v___x_754_ = v_x_620_;
v_isShared_755_ = v_isSharedCheck_760_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_x_752_);
lean_inc(v_ty_751_);
lean_inc(v_b_750_);
lean_inc(v_tgt_749_);
lean_dec(v_x_620_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_760_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_756_ = l_Lean_IR_NormalizeIds_normIndex(v_x_752_, v_x_621_);
lean_dec(v_x_752_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 3, v___x_756_);
v___x_758_ = v___x_754_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_tgt_749_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_b_750_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_ty_751_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
case 18:
{
lean_object* v_tgt_761_; lean_object* v_b_762_; lean_object* v_x_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_771_; 
v_tgt_761_ = lean_ctor_get(v_x_620_, 0);
v_b_762_ = lean_ctor_get(v_x_620_, 1);
v_x_763_ = lean_ctor_get(v_x_620_, 2);
v_isSharedCheck_771_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_771_ == 0)
{
v___x_765_ = v_x_620_;
v_isShared_766_ = v_isSharedCheck_771_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_x_763_);
lean_inc(v_b_762_);
lean_inc(v_tgt_761_);
lean_dec(v_x_620_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_771_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_767_ = l_Lean_IR_NormalizeIds_normIndex(v_x_763_, v_x_621_);
lean_dec(v_x_763_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 2, v___x_767_);
v___x_769_ = v___x_765_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(18, 3, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_tgt_761_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_b_762_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
case 11:
{
return v_x_620_;
}
case 12:
{
return v_x_620_;
}
case 13:
{
return v_x_620_;
}
case 14:
{
return v_x_620_;
}
case 15:
{
return v_x_620_;
}
case 16:
{
return v_x_620_;
}
case 17:
{
return v_x_620_;
}
default: 
{
lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec(v_x_620_);
v___x_772_ = lean_obj_once(&l_Lean_IR_NormalizeIds_normExpr___closed__3, &l_Lean_IR_NormalizeIds_normExpr___closed__3_once, _init_l_Lean_IR_NormalizeIds_normExpr___closed__3);
v___x_773_ = l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0(v___x_772_);
return v___x_773_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normExpr___boxed(lean_object* v_x_774_, lean_object* v_x_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_IR_NormalizeIds_normExpr(v_x_774_, v_x_775_);
lean_dec(v_x_775_);
return v_res_776_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_NormalizeIds_withVar___redArg___lam__0(lean_object* v_x_777_, lean_object* v_y_778_){
_start:
{
uint8_t v___x_779_; 
v___x_779_ = lean_nat_dec_lt(v_x_777_, v_y_778_);
if (v___x_779_ == 0)
{
uint8_t v___x_780_; 
v___x_780_ = lean_nat_dec_eq(v_x_777_, v_y_778_);
if (v___x_780_ == 0)
{
uint8_t v___x_781_; 
v___x_781_ = 2;
return v___x_781_;
}
else
{
uint8_t v___x_782_; 
v___x_782_ = 1;
return v___x_782_;
}
}
else
{
uint8_t v___x_783_; 
v___x_783_ = 0;
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg___lam__0___boxed(lean_object* v_x_784_, lean_object* v_y_785_){
_start:
{
uint8_t v_res_786_; lean_object* v_r_787_; 
v_res_786_ = l_Lean_IR_NormalizeIds_withVar___redArg___lam__0(v_x_784_, v_y_785_);
lean_dec(v_y_785_);
lean_dec(v_x_784_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg(lean_object* v_x_789_, lean_object* v_k_790_, lean_object* v_m_791_, lean_object* v_a_792_){
_start:
{
lean_object* v___f_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___f_793_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_794_ = lean_unsigned_to_nat(1u);
v___x_795_ = lean_nat_add(v_a_792_, v___x_794_);
lean_inc(v_m_791_);
lean_inc(v_a_792_);
v___x_796_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_793_, v_x_789_, v_a_792_, v_m_791_);
v___x_797_ = lean_apply_3(v_k_790_, v_a_792_, v___x_796_, v___x_795_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___redArg___boxed(lean_object* v_x_798_, lean_object* v_k_799_, lean_object* v_m_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_IR_NormalizeIds_withVar___redArg(v_x_798_, v_k_799_, v_m_800_, v_a_801_);
lean_dec(v_m_800_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar(lean_object* v_00_u03b1_803_, lean_object* v_x_804_, lean_object* v_k_805_, lean_object* v_m_806_, lean_object* v_a_807_){
_start:
{
lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___f_808_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_809_ = lean_unsigned_to_nat(1u);
v___x_810_ = lean_nat_add(v_a_807_, v___x_809_);
lean_inc(v_m_806_);
lean_inc(v_a_807_);
v___x_811_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_808_, v_x_804_, v_a_807_, v_m_806_);
v___x_812_ = lean_apply_3(v_k_805_, v_a_807_, v___x_811_, v___x_810_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___boxed(lean_object* v_00_u03b1_813_, lean_object* v_x_814_, lean_object* v_k_815_, lean_object* v_m_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_IR_NormalizeIds_withVar(v_00_u03b1_813_, v_x_814_, v_k_815_, v_m_816_, v_a_817_);
lean_dec(v_m_816_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___redArg(lean_object* v_x_819_, lean_object* v_k_820_, lean_object* v_m_821_, lean_object* v_a_822_){
_start:
{
lean_object* v___f_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___f_823_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_824_ = lean_unsigned_to_nat(1u);
v___x_825_ = lean_nat_add(v_a_822_, v___x_824_);
lean_inc(v_m_821_);
lean_inc(v_a_822_);
v___x_826_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_823_, v_x_819_, v_a_822_, v_m_821_);
v___x_827_ = lean_apply_3(v_k_820_, v_a_822_, v___x_826_, v___x_825_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___redArg___boxed(lean_object* v_x_828_, lean_object* v_k_829_, lean_object* v_m_830_, lean_object* v_a_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_IR_NormalizeIds_withJP___redArg(v_x_828_, v_k_829_, v_m_830_, v_a_831_);
lean_dec(v_m_830_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP(lean_object* v_00_u03b1_833_, lean_object* v_x_834_, lean_object* v_k_835_, lean_object* v_m_836_, lean_object* v_a_837_){
_start:
{
lean_object* v___f_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___f_838_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withVar___redArg___closed__0));
v___x_839_ = lean_unsigned_to_nat(1u);
v___x_840_ = lean_nat_add(v_a_837_, v___x_839_);
lean_inc(v_m_836_);
lean_inc(v_a_837_);
v___x_841_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_838_, v_x_834_, v_a_837_, v_m_836_);
v___x_842_ = lean_apply_3(v_k_835_, v_a_837_, v___x_841_, v___x_840_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___boxed(lean_object* v_00_u03b1_843_, lean_object* v_x_844_, lean_object* v_k_845_, lean_object* v_m_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_IR_NormalizeIds_withJP(v_00_u03b1_843_, v_x_844_, v_k_845_, v_m_846_, v_a_847_);
lean_dec(v_m_846_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__0(lean_object* v_fst_849_, lean_object* v_x_850_){
_start:
{
lean_object* v_x_851_; uint8_t v_borrow_852_; lean_object* v_ty_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_861_; 
v_x_851_ = lean_ctor_get(v_x_850_, 0);
v_borrow_852_ = lean_ctor_get_uint8(v_x_850_, sizeof(void*)*2);
v_ty_853_ = lean_ctor_get(v_x_850_, 1);
v_isSharedCheck_861_ = !lean_is_exclusive(v_x_850_);
if (v_isSharedCheck_861_ == 0)
{
v___x_855_ = v_x_850_;
v_isShared_856_ = v_isSharedCheck_861_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_ty_853_);
lean_inc(v_x_851_);
lean_dec(v_x_850_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_861_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_857_ = l_Lean_IR_NormalizeIds_normIndex(v_x_851_, v_fst_849_);
lean_dec(v_x_851_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_857_);
v___x_859_ = v___x_855_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_ty_853_);
lean_ctor_set_uint8(v_reuseFailAlloc_860_, sizeof(void*)*2, v_borrow_852_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed(lean_object* v_fst_862_, lean_object* v_x_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lean_IR_NormalizeIds_withParams___redArg___lam__0(v_fst_862_, v_x_863_);
lean_dec(v_fst_862_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___lam__2(lean_object* v___f_865_, lean_object* v_m_866_, lean_object* v_p_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_x_869_ = lean_ctor_get(v_p_867_, 0);
lean_inc(v_x_869_);
lean_dec_ref(v_p_867_);
v___x_870_ = lean_unsigned_to_nat(1u);
v___x_871_ = lean_nat_add(v___y_868_, v___x_870_);
v___x_872_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_865_, v_x_869_, v___y_868_, v_m_866_);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v___x_871_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg(lean_object* v_ps_876_, lean_object* v_k_877_, lean_object* v_m_878_, lean_object* v_a_879_){
_start:
{
lean_object* v___f_880_; lean_object* v___f_881_; lean_object* v___f_882_; lean_object* v___f_883_; lean_object* v___f_884_; lean_object* v___f_885_; lean_object* v___f_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v_fst_891_; lean_object* v_snd_892_; lean_object* v___y_899_; lean_object* v___f_902_; lean_object* v___f_903_; lean_object* v___f_904_; lean_object* v___f_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v___f_880_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__0));
v___f_881_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__1));
v___f_882_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__2));
v___f_883_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__3));
v___f_884_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__4));
v___f_885_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__5));
v___f_886_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__6));
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v___f_880_);
lean_ctor_set(v___x_887_, 1, v___f_881_);
v___x_888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v___f_882_);
lean_ctor_set(v___x_888_, 2, v___f_883_);
lean_ctor_set(v___x_888_, 3, v___f_884_);
lean_ctor_set(v___x_888_, 4, v___f_885_);
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___f_886_);
lean_inc_ref_n(v___x_889_, 7);
v___f_902_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_902_, 0, v___x_889_);
v___f_903_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_903_, 0, v___x_889_);
v___f_904_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_904_, 0, v___x_889_);
v___f_905_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_905_, 0, v___x_889_);
v___x_906_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_906_, 0, lean_box(0));
lean_closure_set(v___x_906_, 1, lean_box(0));
lean_closure_set(v___x_906_, 2, v___x_889_);
v___x_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v___f_902_);
v___x_908_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_908_, 0, lean_box(0));
lean_closure_set(v___x_908_, 1, lean_box(0));
lean_closure_set(v___x_908_, 2, v___x_889_);
v___x_909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
lean_ctor_set(v___x_909_, 2, v___f_903_);
lean_ctor_set(v___x_909_, 3, v___f_904_);
lean_ctor_set(v___x_909_, 4, v___f_905_);
v___x_910_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_910_, 0, lean_box(0));
lean_closure_set(v___x_910_, 1, lean_box(0));
lean_closure_set(v___x_910_, 2, v___x_889_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_unsigned_to_nat(0u);
v___x_913_ = lean_array_get_size(v_ps_876_);
v___x_914_ = lean_nat_dec_lt(v___x_912_, v___x_913_);
if (v___x_914_ == 0)
{
lean_dec_ref_known(v___x_911_, 2);
lean_inc(v_m_878_);
v_fst_891_ = v_m_878_;
v_snd_892_ = v_a_879_;
goto v___jp_890_;
}
else
{
lean_object* v___f_915_; uint8_t v___x_916_; 
v___f_915_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__0));
v___x_916_ = lean_nat_dec_le(v___x_913_, v___x_913_);
if (v___x_916_ == 0)
{
if (v___x_914_ == 0)
{
lean_dec_ref_known(v___x_911_, 2);
lean_inc(v_m_878_);
v_fst_891_ = v_m_878_;
v_snd_892_ = v_a_879_;
goto v___jp_890_;
}
else
{
size_t v___x_917_; size_t v___x_918_; lean_object* v___x_787__overap_919_; lean_object* v___x_920_; 
v___x_917_ = ((size_t)0ULL);
v___x_918_ = lean_usize_of_nat(v___x_913_);
lean_inc(v_m_878_);
lean_inc_ref(v_ps_876_);
v___x_787__overap_919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_911_, v___f_915_, v_ps_876_, v___x_917_, v___x_918_, v_m_878_);
v___x_920_ = lean_apply_1(v___x_787__overap_919_, v_a_879_);
v___y_899_ = v___x_920_;
goto v___jp_898_;
}
}
else
{
size_t v___x_921_; size_t v___x_922_; lean_object* v___x_791__overap_923_; lean_object* v___x_924_; 
v___x_921_ = ((size_t)0ULL);
v___x_922_ = lean_usize_of_nat(v___x_913_);
lean_inc(v_m_878_);
lean_inc_ref(v_ps_876_);
v___x_791__overap_923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_911_, v___f_915_, v_ps_876_, v___x_921_, v___x_922_, v_m_878_);
v___x_924_ = lean_apply_1(v___x_791__overap_923_, v_a_879_);
v___y_899_ = v___x_924_;
goto v___jp_898_;
}
}
v___jp_890_:
{
lean_object* v___f_893_; size_t v_sz_894_; size_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
lean_inc(v_fst_891_);
v___f_893_ = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_893_, 0, v_fst_891_);
v_sz_894_ = lean_array_size(v_ps_876_);
v___x_895_ = ((size_t)0ULL);
v___x_896_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_889_, v___f_893_, v_sz_894_, v___x_895_, v_ps_876_);
v___x_897_ = lean_apply_3(v_k_877_, v___x_896_, v_fst_891_, v_snd_892_);
return v___x_897_;
}
v___jp_898_:
{
lean_object* v_fst_900_; lean_object* v_snd_901_; 
v_fst_900_ = lean_ctor_get(v___y_899_, 0);
lean_inc(v_fst_900_);
v_snd_901_ = lean_ctor_get(v___y_899_, 1);
lean_inc(v_snd_901_);
lean_dec_ref(v___y_899_);
v_fst_891_ = v_fst_900_;
v_snd_892_ = v_snd_901_;
goto v___jp_890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___redArg___boxed(lean_object* v_ps_925_, lean_object* v_k_926_, lean_object* v_m_927_, lean_object* v_a_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_IR_NormalizeIds_withParams___redArg(v_ps_925_, v_k_926_, v_m_927_, v_a_928_);
lean_dec(v_m_927_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams(lean_object* v_00_u03b1_930_, lean_object* v_ps_931_, lean_object* v_k_932_, lean_object* v_m_933_, lean_object* v_a_934_){
_start:
{
lean_object* v___f_935_; lean_object* v___f_936_; lean_object* v___f_937_; lean_object* v___f_938_; lean_object* v___f_939_; lean_object* v___f_940_; lean_object* v___f_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v_fst_946_; lean_object* v_snd_947_; lean_object* v___y_954_; lean_object* v___f_957_; lean_object* v___f_958_; lean_object* v___f_959_; lean_object* v___f_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
v___f_935_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__0));
v___f_936_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__1));
v___f_937_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__2));
v___f_938_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__3));
v___f_939_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__4));
v___f_940_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__5));
v___f_941_ = ((lean_object*)(l_panic___at___00Lean_IR_NormalizeIds_normExpr_spec__0___closed__6));
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v___f_935_);
lean_ctor_set(v___x_942_, 1, v___f_936_);
v___x_943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v___f_937_);
lean_ctor_set(v___x_943_, 2, v___f_938_);
lean_ctor_set(v___x_943_, 3, v___f_939_);
lean_ctor_set(v___x_943_, 4, v___f_940_);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v___f_941_);
lean_inc_ref_n(v___x_944_, 7);
v___f_957_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_957_, 0, v___x_944_);
v___f_958_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_958_, 0, v___x_944_);
v___f_959_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_959_, 0, v___x_944_);
v___f_960_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_960_, 0, v___x_944_);
v___x_961_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_961_, 0, lean_box(0));
lean_closure_set(v___x_961_, 1, lean_box(0));
lean_closure_set(v___x_961_, 2, v___x_944_);
v___x_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
lean_ctor_set(v___x_962_, 1, v___f_957_);
v___x_963_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_963_, 0, lean_box(0));
lean_closure_set(v___x_963_, 1, lean_box(0));
lean_closure_set(v___x_963_, 2, v___x_944_);
v___x_964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
lean_ctor_set(v___x_964_, 2, v___f_958_);
lean_ctor_set(v___x_964_, 3, v___f_959_);
lean_ctor_set(v___x_964_, 4, v___f_960_);
v___x_965_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_965_, 0, lean_box(0));
lean_closure_set(v___x_965_, 1, lean_box(0));
lean_closure_set(v___x_965_, 2, v___x_944_);
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_968_ = lean_array_get_size(v_ps_931_);
v___x_969_ = lean_nat_dec_lt(v___x_967_, v___x_968_);
if (v___x_969_ == 0)
{
lean_dec_ref_known(v___x_966_, 2);
lean_inc(v_m_933_);
v_fst_946_ = v_m_933_;
v_snd_947_ = v_a_934_;
goto v___jp_945_;
}
else
{
lean_object* v___f_970_; uint8_t v___x_971_; 
v___f_970_ = ((lean_object*)(l_Lean_IR_NormalizeIds_withParams___redArg___closed__0));
v___x_971_ = lean_nat_dec_le(v___x_968_, v___x_968_);
if (v___x_971_ == 0)
{
if (v___x_969_ == 0)
{
lean_dec_ref_known(v___x_966_, 2);
lean_inc(v_m_933_);
v_fst_946_ = v_m_933_;
v_snd_947_ = v_a_934_;
goto v___jp_945_;
}
else
{
size_t v___x_972_; size_t v___x_973_; lean_object* v___x_972__overap_974_; lean_object* v___x_975_; 
v___x_972_ = ((size_t)0ULL);
v___x_973_ = lean_usize_of_nat(v___x_968_);
lean_inc(v_m_933_);
lean_inc_ref(v_ps_931_);
v___x_972__overap_974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_966_, v___f_970_, v_ps_931_, v___x_972_, v___x_973_, v_m_933_);
v___x_975_ = lean_apply_1(v___x_972__overap_974_, v_a_934_);
v___y_954_ = v___x_975_;
goto v___jp_953_;
}
}
else
{
size_t v___x_976_; size_t v___x_977_; lean_object* v___x_975__overap_978_; lean_object* v___x_979_; 
v___x_976_ = ((size_t)0ULL);
v___x_977_ = lean_usize_of_nat(v___x_968_);
lean_inc(v_m_933_);
lean_inc_ref(v_ps_931_);
v___x_975__overap_978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_966_, v___f_970_, v_ps_931_, v___x_976_, v___x_977_, v_m_933_);
v___x_979_ = lean_apply_1(v___x_975__overap_978_, v_a_934_);
v___y_954_ = v___x_979_;
goto v___jp_953_;
}
}
v___jp_945_:
{
lean_object* v___f_948_; size_t v_sz_949_; size_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
lean_inc(v_fst_946_);
v___f_948_ = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withParams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_948_, 0, v_fst_946_);
v_sz_949_ = lean_array_size(v_ps_931_);
v___x_950_ = ((size_t)0ULL);
v___x_951_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_944_, v___f_948_, v_sz_949_, v___x_950_, v_ps_931_);
v___x_952_ = lean_apply_3(v_k_932_, v___x_951_, v_fst_946_, v_snd_947_);
return v___x_952_;
}
v___jp_953_:
{
lean_object* v_fst_955_; lean_object* v_snd_956_; 
v_fst_955_ = lean_ctor_get(v___y_954_, 0);
lean_inc(v_fst_955_);
v_snd_956_ = lean_ctor_get(v___y_954_, 1);
lean_inc(v_snd_956_);
lean_dec_ref(v___y_954_);
v_fst_946_ = v_fst_955_;
v_snd_947_ = v_snd_956_;
goto v___jp_945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___boxed(lean_object* v_00_u03b1_980_, lean_object* v_ps_981_, lean_object* v_k_982_, lean_object* v_m_983_, lean_object* v_a_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_IR_NormalizeIds_withParams(v_00_u03b1_980_, v_ps_981_, v_k_982_, v_m_983_, v_a_984_);
lean_dec(v_m_983_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_instMonadLiftMN___lam__0(lean_object* v_00_u03b1_986_, lean_object* v_x_987_, lean_object* v_m_988_, lean_object* v___y_989_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_apply_1(v_x_987_, v_m_988_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v___y_989_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(lean_object* v_fst_994_, size_t v_sz_995_, size_t v_i_996_, lean_object* v_bs_997_){
_start:
{
uint8_t v___x_998_; 
v___x_998_ = lean_usize_dec_lt(v_i_996_, v_sz_995_);
if (v___x_998_ == 0)
{
return v_bs_997_;
}
else
{
lean_object* v_v_999_; lean_object* v_x_1000_; uint8_t v_borrow_1001_; lean_object* v_ty_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1016_; 
v_v_999_ = lean_array_uget(v_bs_997_, v_i_996_);
v_x_1000_ = lean_ctor_get(v_v_999_, 0);
v_borrow_1001_ = lean_ctor_get_uint8(v_v_999_, sizeof(void*)*2);
v_ty_1002_ = lean_ctor_get(v_v_999_, 1);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_v_999_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1004_ = v_v_999_;
v_isShared_1005_ = v_isSharedCheck_1016_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_ty_1002_);
lean_inc(v_x_1000_);
lean_dec(v_v_999_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1016_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v_bs_x27_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1006_ = lean_unsigned_to_nat(0u);
v_bs_x27_1007_ = lean_array_uset(v_bs_997_, v_i_996_, v___x_1006_);
v___x_1008_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1000_, v_fst_994_);
lean_dec(v_x_1000_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_1008_);
v___x_1010_ = v___x_1004_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_ty_1002_);
lean_ctor_set_uint8(v_reuseFailAlloc_1015_, sizeof(void*)*2, v_borrow_1001_);
v___x_1010_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
size_t v___x_1011_; size_t v___x_1012_; lean_object* v___x_1013_; 
v___x_1011_ = ((size_t)1ULL);
v___x_1012_ = lean_usize_add(v_i_996_, v___x_1011_);
v___x_1013_ = lean_array_uset(v_bs_x27_1007_, v_i_996_, v___x_1010_);
v_i_996_ = v___x_1012_;
v_bs_997_ = v___x_1013_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0___boxed(lean_object* v_fst_1017_, lean_object* v_sz_1018_, lean_object* v_i_1019_, lean_object* v_bs_1020_){
_start:
{
size_t v_sz_boxed_1021_; size_t v_i_boxed_1022_; lean_object* v_res_1023_; 
v_sz_boxed_1021_ = lean_unbox_usize(v_sz_1018_);
lean_dec(v_sz_1018_);
v_i_boxed_1022_ = lean_unbox_usize(v_i_1019_);
lean_dec(v_i_1019_);
v_res_1023_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(v_fst_1017_, v_sz_boxed_1021_, v_i_boxed_1022_, v_bs_1020_);
lean_dec(v_fst_1017_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(lean_object* v_as_1024_, size_t v_i_1025_, size_t v_stop_1026_, lean_object* v_b_1027_, lean_object* v___y_1028_){
_start:
{
uint8_t v___x_1029_; 
v___x_1029_ = lean_usize_dec_eq(v_i_1025_, v_stop_1026_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v_x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; size_t v___x_1035_; size_t v___x_1036_; 
v___x_1030_ = lean_array_uget_borrowed(v_as_1024_, v_i_1025_);
v_x_1031_ = lean_ctor_get(v___x_1030_, 0);
v___x_1032_ = lean_unsigned_to_nat(1u);
v___x_1033_ = lean_nat_add(v___y_1028_, v___x_1032_);
lean_inc(v_x_1031_);
v___x_1034_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_x_1031_, v___y_1028_, v_b_1027_);
v___x_1035_ = ((size_t)1ULL);
v___x_1036_ = lean_usize_add(v_i_1025_, v___x_1035_);
v_i_1025_ = v___x_1036_;
v_b_1027_ = v___x_1034_;
v___y_1028_ = v___x_1033_;
goto _start;
}
else
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v_b_1027_);
lean_ctor_set(v___x_1038_, 1, v___y_1028_);
return v___x_1038_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1___boxed(lean_object* v_as_1039_, lean_object* v_i_1040_, lean_object* v_stop_1041_, lean_object* v_b_1042_, lean_object* v___y_1043_){
_start:
{
size_t v_i_boxed_1044_; size_t v_stop_boxed_1045_; lean_object* v_res_1046_; 
v_i_boxed_1044_ = lean_unbox_usize(v_i_1040_);
lean_dec(v_i_1040_);
v_stop_boxed_1045_ = lean_unbox_usize(v_stop_1041_);
lean_dec(v_stop_1041_);
v_res_1046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_as_1039_, v_i_boxed_1044_, v_stop_boxed_1045_, v_b_1042_, v___y_1043_);
lean_dec_ref(v_as_1039_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normFnBody(lean_object* v_x_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
switch(lean_obj_tag(v_x_1047_))
{
case 19:
{
lean_object* v_j_1050_; lean_object* v_xs_1051_; lean_object* v_v_1052_; lean_object* v_b_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1090_; 
v_j_1050_ = lean_ctor_get(v_x_1047_, 0);
v_xs_1051_ = lean_ctor_get(v_x_1047_, 1);
v_v_1052_ = lean_ctor_get(v_x_1047_, 2);
v_b_1053_ = lean_ctor_get(v_x_1047_, 3);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1055_ = v_x_1047_;
v_isShared_1056_ = v_isSharedCheck_1090_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_b_1053_);
lean_inc(v_v_1052_);
lean_inc(v_xs_1051_);
lean_inc(v_j_1050_);
lean_dec(v_x_1047_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1090_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v_fst_1058_; lean_object* v_snd_1059_; lean_object* v___x_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = lean_array_get_size(v_xs_1051_);
v___x_1084_ = lean_nat_dec_lt(v___x_1082_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_inc(v_a_1048_);
v_fst_1058_ = v_a_1048_;
v_snd_1059_ = v_a_1049_;
goto v___jp_1057_;
}
else
{
size_t v___x_1085_; size_t v___x_1086_; lean_object* v___x_1087_; lean_object* v_fst_1088_; lean_object* v_snd_1089_; 
v___x_1085_ = ((size_t)0ULL);
v___x_1086_ = lean_usize_of_nat(v___x_1083_);
lean_inc(v_a_1048_);
v___x_1087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_1051_, v___x_1085_, v___x_1086_, v_a_1048_, v_a_1049_);
v_fst_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_fst_1088_);
v_snd_1089_ = lean_ctor_get(v___x_1087_, 1);
lean_inc(v_snd_1089_);
lean_dec_ref(v___x_1087_);
v_fst_1058_ = v_fst_1088_;
v_snd_1059_ = v_snd_1089_;
goto v___jp_1057_;
}
v___jp_1057_:
{
lean_object* v___x_1060_; lean_object* v_fst_1061_; lean_object* v_snd_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v_fst_1067_; lean_object* v_snd_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1081_; 
v___x_1060_ = l_Lean_IR_NormalizeIds_normFnBody(v_v_1052_, v_fst_1058_, v_snd_1059_);
v_fst_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_fst_1061_);
v_snd_1062_ = lean_ctor_get(v___x_1060_, 1);
lean_inc_n(v_snd_1062_, 2);
lean_dec_ref(v___x_1060_);
v___x_1063_ = lean_unsigned_to_nat(1u);
v___x_1064_ = lean_nat_add(v_snd_1062_, v___x_1063_);
lean_inc(v_a_1048_);
v___x_1065_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_j_1050_, v_snd_1062_, v_a_1048_);
v___x_1066_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1053_, v___x_1065_, v___x_1064_);
lean_dec(v___x_1065_);
v_fst_1067_ = lean_ctor_get(v___x_1066_, 0);
v_snd_1068_ = lean_ctor_get(v___x_1066_, 1);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1070_ = v___x_1066_;
v_isShared_1071_ = v_isSharedCheck_1081_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_snd_1068_);
lean_inc(v_fst_1067_);
lean_dec(v___x_1066_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1081_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
size_t v_sz_1072_; size_t v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
v_sz_1072_ = lean_array_size(v_xs_1051_);
v___x_1073_ = ((size_t)0ULL);
v___x_1074_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__0(v_fst_1058_, v_sz_1072_, v___x_1073_, v_xs_1051_);
lean_dec(v_fst_1058_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 3, v_fst_1067_);
lean_ctor_set(v___x_1055_, 2, v_fst_1061_);
lean_ctor_set(v___x_1055_, 1, v___x_1074_);
lean_ctor_set(v___x_1055_, 0, v_snd_1062_);
v___x_1076_ = v___x_1055_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(19, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_snd_1062_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v_fst_1061_);
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v_fst_1067_);
v___x_1076_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1078_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1076_);
v___x_1078_ = v___x_1070_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_snd_1068_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
}
case 20:
{
lean_object* v_x_1091_; lean_object* v_i_1092_; lean_object* v_y_1093_; lean_object* v_b_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1113_; 
v_x_1091_ = lean_ctor_get(v_x_1047_, 0);
v_i_1092_ = lean_ctor_get(v_x_1047_, 1);
v_y_1093_ = lean_ctor_get(v_x_1047_, 2);
v_b_1094_ = lean_ctor_get(v_x_1047_, 3);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1096_ = v_x_1047_;
v_isShared_1097_ = v_isSharedCheck_1113_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_b_1094_);
lean_inc(v_y_1093_);
lean_inc(v_i_1092_);
lean_inc(v_x_1091_);
lean_dec(v_x_1047_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1113_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v_fst_1101_; lean_object* v_snd_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1112_; 
v___x_1098_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1091_, v_a_1048_);
lean_dec(v_x_1091_);
v___x_1099_ = l_Lean_IR_NormalizeIds_normArg(v_y_1093_, v_a_1048_);
v___x_1100_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1094_, v_a_1048_, v_a_1049_);
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
v_reuseFailAlloc_1111_ = lean_alloc_ctor(20, 4, 0);
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
case 22:
{
lean_object* v_x_1114_; lean_object* v_i_1115_; lean_object* v_y_1116_; lean_object* v_b_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1136_; 
v_x_1114_ = lean_ctor_get(v_x_1047_, 0);
v_i_1115_ = lean_ctor_get(v_x_1047_, 1);
v_y_1116_ = lean_ctor_get(v_x_1047_, 2);
v_b_1117_ = lean_ctor_get(v_x_1047_, 3);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1119_ = v_x_1047_;
v_isShared_1120_ = v_isSharedCheck_1136_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_b_1117_);
lean_inc(v_y_1116_);
lean_inc(v_i_1115_);
lean_inc(v_x_1114_);
lean_dec(v_x_1047_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1136_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v_fst_1124_; lean_object* v_snd_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1135_; 
v___x_1121_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1114_, v_a_1048_);
lean_dec(v_x_1114_);
v___x_1122_ = l_Lean_IR_NormalizeIds_normIndex(v_y_1116_, v_a_1048_);
lean_dec(v_y_1116_);
v___x_1123_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1117_, v_a_1048_, v_a_1049_);
v_fst_1124_ = lean_ctor_get(v___x_1123_, 0);
v_snd_1125_ = lean_ctor_get(v___x_1123_, 1);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1127_ = v___x_1123_;
v_isShared_1128_ = v_isSharedCheck_1135_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_snd_1125_);
lean_inc(v_fst_1124_);
lean_dec(v___x_1123_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1135_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 3, v_fst_1124_);
lean_ctor_set(v___x_1119_, 2, v___x_1122_);
lean_ctor_set(v___x_1119_, 0, v___x_1121_);
v___x_1130_ = v___x_1119_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(22, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1121_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_i_1115_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v_fst_1124_);
v___x_1130_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1132_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1130_);
v___x_1132_ = v___x_1127_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_snd_1125_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
case 23:
{
lean_object* v_x_1137_; lean_object* v_i_1138_; lean_object* v_offset_1139_; lean_object* v_y_1140_; lean_object* v_ty_1141_; lean_object* v_b_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1161_; 
v_x_1137_ = lean_ctor_get(v_x_1047_, 0);
v_i_1138_ = lean_ctor_get(v_x_1047_, 1);
v_offset_1139_ = lean_ctor_get(v_x_1047_, 2);
v_y_1140_ = lean_ctor_get(v_x_1047_, 3);
v_ty_1141_ = lean_ctor_get(v_x_1047_, 4);
v_b_1142_ = lean_ctor_get(v_x_1047_, 5);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1144_ = v_x_1047_;
v_isShared_1145_ = v_isSharedCheck_1161_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_b_1142_);
lean_inc(v_ty_1141_);
lean_inc(v_y_1140_);
lean_inc(v_offset_1139_);
lean_inc(v_i_1138_);
lean_inc(v_x_1137_);
lean_dec(v_x_1047_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1161_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v_fst_1149_; lean_object* v_snd_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1160_; 
v___x_1146_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1137_, v_a_1048_);
lean_dec(v_x_1137_);
v___x_1147_ = l_Lean_IR_NormalizeIds_normIndex(v_y_1140_, v_a_1048_);
lean_dec(v_y_1140_);
v___x_1148_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1142_, v_a_1048_, v_a_1049_);
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
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 5, v_fst_1149_);
lean_ctor_set(v___x_1144_, 3, v___x_1147_);
lean_ctor_set(v___x_1144_, 0, v___x_1146_);
v___x_1155_ = v___x_1144_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(23, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_i_1138_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_offset_1139_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1159_, 4, v_ty_1141_);
lean_ctor_set(v_reuseFailAlloc_1159_, 5, v_fst_1149_);
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
case 21:
{
lean_object* v_x_1162_; lean_object* v_cidx_1163_; lean_object* v_b_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1182_; 
v_x_1162_ = lean_ctor_get(v_x_1047_, 0);
v_cidx_1163_ = lean_ctor_get(v_x_1047_, 1);
v_b_1164_ = lean_ctor_get(v_x_1047_, 2);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1166_ = v_x_1047_;
v_isShared_1167_ = v_isSharedCheck_1182_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_b_1164_);
lean_inc(v_cidx_1163_);
lean_inc(v_x_1162_);
lean_dec(v_x_1047_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1182_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v_fst_1170_; lean_object* v_snd_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1181_; 
v___x_1168_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1162_, v_a_1048_);
lean_dec(v_x_1162_);
v___x_1169_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1164_, v_a_1048_, v_a_1049_);
v_fst_1170_ = lean_ctor_get(v___x_1169_, 0);
v_snd_1171_ = lean_ctor_get(v___x_1169_, 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1173_ = v___x_1169_;
v_isShared_1174_ = v_isSharedCheck_1181_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_snd_1171_);
lean_inc(v_fst_1170_);
lean_dec(v___x_1169_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1181_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 2, v_fst_1170_);
lean_ctor_set(v___x_1166_, 0, v___x_1168_);
v___x_1176_ = v___x_1166_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(21, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_cidx_1163_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v_fst_1170_);
v___x_1176_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
lean_object* v___x_1178_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v___x_1176_);
v___x_1178_ = v___x_1173_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_snd_1171_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
case 24:
{
lean_object* v_x_1183_; lean_object* v_n_1184_; uint8_t v_c_1185_; uint8_t v_persistent_1186_; lean_object* v_b_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1205_; 
v_x_1183_ = lean_ctor_get(v_x_1047_, 0);
v_n_1184_ = lean_ctor_get(v_x_1047_, 1);
v_c_1185_ = lean_ctor_get_uint8(v_x_1047_, sizeof(void*)*3);
v_persistent_1186_ = lean_ctor_get_uint8(v_x_1047_, sizeof(void*)*3 + 1);
v_b_1187_ = lean_ctor_get(v_x_1047_, 2);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1189_ = v_x_1047_;
v_isShared_1190_ = v_isSharedCheck_1205_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_b_1187_);
lean_inc(v_n_1184_);
lean_inc(v_x_1183_);
lean_dec(v_x_1047_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1205_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v_fst_1193_; lean_object* v_snd_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1204_; 
v___x_1191_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1183_, v_a_1048_);
lean_dec(v_x_1183_);
v___x_1192_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1187_, v_a_1048_, v_a_1049_);
v_fst_1193_ = lean_ctor_get(v___x_1192_, 0);
v_snd_1194_ = lean_ctor_get(v___x_1192_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1196_ = v___x_1192_;
v_isShared_1197_ = v_isSharedCheck_1204_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_snd_1194_);
lean_inc(v_fst_1193_);
lean_dec(v___x_1192_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1204_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 2, v_fst_1193_);
lean_ctor_set(v___x_1189_, 0, v___x_1191_);
v___x_1199_ = v___x_1189_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(24, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_n_1184_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_fst_1193_);
lean_ctor_set_uint8(v_reuseFailAlloc_1203_, sizeof(void*)*3, v_c_1185_);
lean_ctor_set_uint8(v_reuseFailAlloc_1203_, sizeof(void*)*3 + 1, v_persistent_1186_);
v___x_1199_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1201_; 
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1199_);
v___x_1201_ = v___x_1196_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_snd_1194_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
case 25:
{
lean_object* v_x_1206_; lean_object* v_n_1207_; uint8_t v_c_1208_; uint8_t v_persistent_1209_; lean_object* v_b_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1228_; 
v_x_1206_ = lean_ctor_get(v_x_1047_, 0);
v_n_1207_ = lean_ctor_get(v_x_1047_, 1);
v_c_1208_ = lean_ctor_get_uint8(v_x_1047_, sizeof(void*)*3);
v_persistent_1209_ = lean_ctor_get_uint8(v_x_1047_, sizeof(void*)*3 + 1);
v_b_1210_ = lean_ctor_get(v_x_1047_, 2);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1212_ = v_x_1047_;
v_isShared_1213_ = v_isSharedCheck_1228_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_b_1210_);
lean_inc(v_n_1207_);
lean_inc(v_x_1206_);
lean_dec(v_x_1047_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1228_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v_fst_1216_; lean_object* v_snd_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1227_; 
v___x_1214_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1206_, v_a_1048_);
lean_dec(v_x_1206_);
v___x_1215_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1210_, v_a_1048_, v_a_1049_);
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
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 2, v_fst_1216_);
lean_ctor_set(v___x_1212_, 0, v___x_1214_);
v___x_1222_ = v___x_1212_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(25, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_n_1207_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_fst_1216_);
lean_ctor_set_uint8(v_reuseFailAlloc_1226_, sizeof(void*)*3, v_c_1208_);
lean_ctor_set_uint8(v_reuseFailAlloc_1226_, sizeof(void*)*3 + 1, v_persistent_1209_);
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
case 26:
{
lean_object* v_x_1229_; lean_object* v_b_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1248_; 
v_x_1229_ = lean_ctor_get(v_x_1047_, 0);
v_b_1230_ = lean_ctor_get(v_x_1047_, 1);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1232_ = v_x_1047_;
v_isShared_1233_ = v_isSharedCheck_1248_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_b_1230_);
lean_inc(v_x_1229_);
lean_dec(v_x_1047_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1248_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v_fst_1236_; lean_object* v_snd_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1247_; 
v___x_1234_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1229_, v_a_1048_);
lean_dec(v_x_1229_);
v___x_1235_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1230_, v_a_1048_, v_a_1049_);
v_fst_1236_ = lean_ctor_get(v___x_1235_, 0);
v_snd_1237_ = lean_ctor_get(v___x_1235_, 1);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1239_ = v___x_1235_;
v_isShared_1240_ = v_isSharedCheck_1247_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_snd_1237_);
lean_inc(v_fst_1236_);
lean_dec(v___x_1235_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1247_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 1, v_fst_1236_);
lean_ctor_set(v___x_1232_, 0, v___x_1234_);
v___x_1242_ = v___x_1232_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(26, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_fst_1236_);
v___x_1242_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1244_; 
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1242_);
v___x_1244_ = v___x_1239_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_snd_1237_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
case 27:
{
lean_object* v_tid_1249_; lean_object* v_x_1250_; lean_object* v_xType_1251_; lean_object* v_cs_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1272_; 
v_tid_1249_ = lean_ctor_get(v_x_1047_, 0);
v_x_1250_ = lean_ctor_get(v_x_1047_, 1);
v_xType_1251_ = lean_ctor_get(v_x_1047_, 2);
v_cs_1252_ = lean_ctor_get(v_x_1047_, 3);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1254_ = v_x_1047_;
v_isShared_1255_ = v_isSharedCheck_1272_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_cs_1252_);
lean_inc(v_xType_1251_);
lean_inc(v_x_1250_);
lean_inc(v_tid_1249_);
lean_dec(v_x_1047_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1272_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; size_t v_sz_1257_; size_t v___x_1258_; lean_object* v___x_1259_; lean_object* v_fst_1260_; lean_object* v_snd_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1271_; 
v___x_1256_ = l_Lean_IR_NormalizeIds_normIndex(v_x_1250_, v_a_1048_);
lean_dec(v_x_1250_);
v_sz_1257_ = lean_array_size(v_cs_1252_);
v___x_1258_ = ((size_t)0ULL);
v___x_1259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(v_sz_1257_, v___x_1258_, v_cs_1252_, v_a_1048_, v_a_1049_);
v_fst_1260_ = lean_ctor_get(v___x_1259_, 0);
v_snd_1261_ = lean_ctor_get(v___x_1259_, 1);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1263_ = v___x_1259_;
v_isShared_1264_ = v_isSharedCheck_1271_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_snd_1261_);
lean_inc(v_fst_1260_);
lean_dec(v___x_1259_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1271_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 3, v_fst_1260_);
lean_ctor_set(v___x_1254_, 1, v___x_1256_);
v___x_1266_ = v___x_1254_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(27, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_tid_1249_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v___x_1256_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_xType_1251_);
lean_ctor_set(v_reuseFailAlloc_1270_, 3, v_fst_1260_);
v___x_1266_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1268_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1266_);
v___x_1268_ = v___x_1263_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_snd_1261_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
case 29:
{
lean_object* v_j_1273_; lean_object* v_ys_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1284_; 
v_j_1273_ = lean_ctor_get(v_x_1047_, 0);
v_ys_1274_ = lean_ctor_get(v_x_1047_, 1);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1276_ = v_x_1047_;
v_isShared_1277_ = v_isSharedCheck_1284_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_ys_1274_);
lean_inc(v_j_1273_);
lean_dec(v_x_1047_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1284_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1278_ = l_Lean_IR_NormalizeIds_normIndex(v_j_1273_, v_a_1048_);
lean_dec(v_j_1273_);
v___x_1279_ = l_Lean_IR_NormalizeIds_normArgs(v_ys_1274_, v_a_1048_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 1, v___x_1279_);
lean_ctor_set(v___x_1276_, 0, v___x_1278_);
v___x_1281_ = v___x_1276_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(29, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
lean_ctor_set(v___x_1282_, 1, v_a_1049_);
return v___x_1282_;
}
}
}
case 28:
{
lean_object* v_x_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1294_; 
v_x_1285_ = lean_ctor_get(v_x_1047_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1287_ = v_x_1047_;
v_isShared_1288_ = v_isSharedCheck_1294_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_x_1285_);
lean_dec(v_x_1047_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1294_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1289_ = l_Lean_IR_NormalizeIds_normArg(v_x_1285_, v_a_1048_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1289_);
v___x_1291_ = v___x_1287_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(28, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
lean_ctor_set(v___x_1292_, 1, v_a_1049_);
return v___x_1292_;
}
}
}
case 30:
{
lean_object* v___x_1295_; 
v___x_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1295_, 0, v_x_1047_);
lean_ctor_set(v___x_1295_, 1, v_a_1049_);
return v___x_1295_;
}
default: 
{
lean_object* v_x_1296_; lean_object* v_b_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v_fst_1302_; lean_object* v_snd_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1313_; 
v_x_1296_ = l_Lean_IR_FnBody_targetVar(v_x_1047_);
v_b_1297_ = l_Lean_IR_FnBody_body(v_x_1047_);
v___x_1298_ = lean_unsigned_to_nat(1u);
v___x_1299_ = lean_nat_add(v_a_1049_, v___x_1298_);
lean_inc(v_a_1048_);
lean_inc(v_a_1049_);
v___x_1300_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_UniqueIds_checkId_spec__1___redArg(v_x_1296_, v_a_1049_, v_a_1048_);
v___x_1301_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1297_, v___x_1300_, v___x_1299_);
lean_dec(v___x_1300_);
v_fst_1302_ = lean_ctor_get(v___x_1301_, 0);
v_snd_1303_ = lean_ctor_get(v___x_1301_, 1);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1305_ = v___x_1301_;
v_isShared_1306_ = v_isSharedCheck_1313_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_snd_1303_);
lean_inc(v_fst_1302_);
lean_dec(v___x_1301_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1313_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1311_; 
v___x_1307_ = l_Lean_IR_NormalizeIds_normExpr(v_x_1047_, v_a_1048_);
v___x_1308_ = l_Lean_IR_FnBody_setTargetVar(v___x_1307_, v_a_1049_);
v___x_1309_ = l_Lean_IR_FnBody_setBody(v___x_1308_, v_fst_1302_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v___x_1309_);
v___x_1311_ = v___x_1305_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_snd_1303_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(size_t v_sz_1314_, size_t v_i_1315_, lean_object* v_bs_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
uint8_t v___x_1319_; 
v___x_1319_ = lean_usize_dec_lt(v_i_1315_, v_sz_1314_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v_bs_1316_);
lean_ctor_set(v___x_1320_, 1, v___y_1318_);
return v___x_1320_;
}
else
{
lean_object* v_v_1321_; lean_object* v___x_1322_; lean_object* v_bs_x27_1323_; lean_object* v_fst_1325_; lean_object* v_snd_1326_; 
v_v_1321_ = lean_array_uget(v_bs_1316_, v_i_1315_);
v___x_1322_ = lean_unsigned_to_nat(0u);
v_bs_x27_1323_ = lean_array_uset(v_bs_1316_, v_i_1315_, v___x_1322_);
if (lean_obj_tag(v_v_1321_) == 0)
{
lean_object* v_info_1331_; lean_object* v_b_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1342_; 
v_info_1331_ = lean_ctor_get(v_v_1321_, 0);
v_b_1332_ = lean_ctor_get(v_v_1321_, 1);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_v_1321_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1334_ = v_v_1321_;
v_isShared_1335_ = v_isSharedCheck_1342_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_b_1332_);
lean_inc(v_info_1331_);
lean_dec(v_v_1321_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1342_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; lean_object* v_fst_1337_; lean_object* v_snd_1338_; lean_object* v___x_1340_; 
v___x_1336_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1332_, v___y_1317_, v___y_1318_);
v_fst_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_fst_1337_);
v_snd_1338_ = lean_ctor_get(v___x_1336_, 1);
lean_inc(v_snd_1338_);
lean_dec_ref(v___x_1336_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 1, v_fst_1337_);
v___x_1340_ = v___x_1334_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_info_1331_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_fst_1337_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
v_fst_1325_ = v___x_1340_;
v_snd_1326_ = v_snd_1338_;
goto v___jp_1324_;
}
}
}
else
{
lean_object* v_b_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1353_; 
v_b_1343_ = lean_ctor_get(v_v_1321_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_v_1321_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1345_ = v_v_1321_;
v_isShared_1346_ = v_isSharedCheck_1353_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_b_1343_);
lean_dec(v_v_1321_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1353_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v_fst_1348_; lean_object* v_snd_1349_; lean_object* v___x_1351_; 
v___x_1347_ = l_Lean_IR_NormalizeIds_normFnBody(v_b_1343_, v___y_1317_, v___y_1318_);
v_fst_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_fst_1348_);
v_snd_1349_ = lean_ctor_get(v___x_1347_, 1);
lean_inc(v_snd_1349_);
lean_dec_ref(v___x_1347_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v_fst_1348_);
v___x_1351_ = v___x_1345_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_fst_1348_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
v_fst_1325_ = v___x_1351_;
v_snd_1326_ = v_snd_1349_;
goto v___jp_1324_;
}
}
}
v___jp_1324_:
{
size_t v___x_1327_; size_t v___x_1328_; lean_object* v___x_1329_; 
v___x_1327_ = ((size_t)1ULL);
v___x_1328_ = lean_usize_add(v_i_1315_, v___x_1327_);
v___x_1329_ = lean_array_uset(v_bs_x27_1323_, v_i_1315_, v_fst_1325_);
v_i_1315_ = v___x_1328_;
v_bs_1316_ = v___x_1329_;
v___y_1318_ = v_snd_1326_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2___boxed(lean_object* v_sz_1354_, lean_object* v_i_1355_, lean_object* v_bs_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
size_t v_sz_boxed_1359_; size_t v_i_boxed_1360_; lean_object* v_res_1361_; 
v_sz_boxed_1359_ = lean_unbox_usize(v_sz_1354_);
lean_dec(v_sz_1354_);
v_i_boxed_1360_ = lean_unbox_usize(v_i_1355_);
lean_dec(v_i_1355_);
v_res_1361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_NormalizeIds_normFnBody_spec__2(v_sz_boxed_1359_, v_i_boxed_1360_, v_bs_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1357_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normFnBody___boxed(lean_object* v_x_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_IR_NormalizeIds_normFnBody(v_x_1362_, v_a_1363_, v_a_1364_);
lean_dec(v_a_1363_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normDecl(lean_object* v_d_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
if (lean_obj_tag(v_d_1366_) == 0)
{
lean_object* v_xs_1369_; lean_object* v_body_1370_; lean_object* v_fst_1372_; lean_object* v_snd_1373_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v_xs_1369_ = lean_ctor_get(v_d_1366_, 1);
v_body_1370_ = lean_ctor_get(v_d_1366_, 3);
v___x_1385_ = lean_unsigned_to_nat(0u);
v___x_1386_ = lean_array_get_size(v_xs_1369_);
v___x_1387_ = lean_nat_dec_lt(v___x_1385_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_inc(v_a_1367_);
v_fst_1372_ = v_a_1367_;
v_snd_1373_ = v_a_1368_;
goto v___jp_1371_;
}
else
{
size_t v___x_1388_; size_t v___x_1389_; lean_object* v___x_1390_; lean_object* v_fst_1391_; lean_object* v_snd_1392_; 
v___x_1388_ = ((size_t)0ULL);
v___x_1389_ = lean_usize_of_nat(v___x_1386_);
lean_inc(v_a_1367_);
v___x_1390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_NormalizeIds_normFnBody_spec__1(v_xs_1369_, v___x_1388_, v___x_1389_, v_a_1367_, v_a_1368_);
v_fst_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_fst_1391_);
v_snd_1392_ = lean_ctor_get(v___x_1390_, 1);
lean_inc(v_snd_1392_);
lean_dec_ref(v___x_1390_);
v_fst_1372_ = v_fst_1391_;
v_snd_1373_ = v_snd_1392_;
goto v___jp_1371_;
}
v___jp_1371_:
{
lean_object* v___x_1374_; lean_object* v_fst_1375_; lean_object* v_snd_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1384_; 
lean_inc(v_body_1370_);
v___x_1374_ = l_Lean_IR_NormalizeIds_normFnBody(v_body_1370_, v_fst_1372_, v_snd_1373_);
lean_dec(v_fst_1372_);
v_fst_1375_ = lean_ctor_get(v___x_1374_, 0);
v_snd_1376_ = lean_ctor_get(v___x_1374_, 1);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1378_ = v___x_1374_;
v_isShared_1379_ = v_isSharedCheck_1384_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_snd_1376_);
lean_inc(v_fst_1375_);
lean_dec(v___x_1374_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1384_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1380_; lean_object* v___x_1382_; 
v___x_1380_ = l_Lean_IR_Decl_updateBody_x21(v_d_1366_, v_fst_1375_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v___x_1380_);
v___x_1382_ = v___x_1378_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_snd_1376_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
else
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v_d_1366_);
lean_ctor_set(v___x_1393_, 1, v_a_1368_);
return v___x_1393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normDecl___boxed(lean_object* v_d_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_IR_NormalizeIds_normDecl(v_d_1394_, v_a_1395_, v_a_1396_);
lean_dec(v_a_1395_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_normalizeIds(lean_object* v_d_1398_){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v_fst_1402_; 
v___x_1399_ = lean_box(1);
v___x_1400_ = lean_unsigned_to_nat(1u);
v___x_1401_ = l_Lean_IR_NormalizeIds_normDecl(v_d_1398_, v___x_1399_, v___x_1400_);
v_fst_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_fst_1402_);
lean_dec_ref(v___x_1401_);
return v_fst_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArg(lean_object* v_f_1403_, lean_object* v_x_1404_){
_start:
{
if (lean_obj_tag(v_x_1404_) == 0)
{
lean_object* v_id_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1413_; 
v_id_1405_ = lean_ctor_get(v_x_1404_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_x_1404_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1407_ = v_x_1404_;
v_isShared_1408_ = v_isSharedCheck_1413_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_id_1405_);
lean_dec(v_x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1413_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1409_ = lean_apply_1(v_f_1403_, v_id_1405_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v___x_1409_);
v___x_1411_ = v___x_1407_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
else
{
lean_dec_ref(v_f_1403_);
return v_x_1404_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(lean_object* v_f_1414_, size_t v_sz_1415_, size_t v_i_1416_, lean_object* v_bs_1417_){
_start:
{
uint8_t v___x_1418_; 
v___x_1418_ = lean_usize_dec_lt(v_i_1416_, v_sz_1415_);
if (v___x_1418_ == 0)
{
lean_dec_ref(v_f_1414_);
return v_bs_1417_;
}
else
{
lean_object* v_v_1419_; lean_object* v___x_1420_; lean_object* v_bs_x27_1421_; lean_object* v___y_1423_; 
v_v_1419_ = lean_array_uget(v_bs_1417_, v_i_1416_);
v___x_1420_ = lean_unsigned_to_nat(0u);
v_bs_x27_1421_ = lean_array_uset(v_bs_1417_, v_i_1416_, v___x_1420_);
if (lean_obj_tag(v_v_1419_) == 0)
{
lean_object* v_id_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1436_; 
v_id_1428_ = lean_ctor_get(v_v_1419_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v_v_1419_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1430_ = v_v_1419_;
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_id_1428_);
lean_dec(v_v_1419_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
lean_inc_ref(v_f_1414_);
v___x_1432_ = lean_apply_1(v_f_1414_, v_id_1428_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1432_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
v___y_1423_ = v___x_1434_;
goto v___jp_1422_;
}
}
}
else
{
v___y_1423_ = v_v_1419_;
goto v___jp_1422_;
}
v___jp_1422_:
{
size_t v___x_1424_; size_t v___x_1425_; lean_object* v___x_1426_; 
v___x_1424_ = ((size_t)1ULL);
v___x_1425_ = lean_usize_add(v_i_1416_, v___x_1424_);
v___x_1426_ = lean_array_uset(v_bs_x27_1421_, v_i_1416_, v___y_1423_);
v_i_1416_ = v___x_1425_;
v_bs_1417_ = v___x_1426_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0___boxed(lean_object* v_f_1437_, lean_object* v_sz_1438_, lean_object* v_i_1439_, lean_object* v_bs_1440_){
_start:
{
size_t v_sz_boxed_1441_; size_t v_i_boxed_1442_; lean_object* v_res_1443_; 
v_sz_boxed_1441_ = lean_unbox_usize(v_sz_1438_);
lean_dec(v_sz_1438_);
v_i_boxed_1442_ = lean_unbox_usize(v_i_1439_);
lean_dec(v_i_1439_);
v_res_1443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(v_f_1437_, v_sz_boxed_1441_, v_i_boxed_1442_, v_bs_1440_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArgs(lean_object* v_f_1444_, lean_object* v_as_1445_){
_start:
{
size_t v_sz_1446_; size_t v___x_1447_; lean_object* v___x_1448_; 
v_sz_1446_ = lean_array_size(v_as_1445_);
v___x_1447_ = ((size_t)0ULL);
v___x_1448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapArgs_spec__0(v_f_1444_, v_sz_1446_, v___x_1447_, v_as_1445_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapFnBody(lean_object* v_f_1449_, lean_object* v_x_1450_){
_start:
{
switch(lean_obj_tag(v_x_1450_))
{
case 0:
{
lean_object* v_tgt_1451_; lean_object* v_b_1452_; lean_object* v_i_1453_; lean_object* v_ys_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1463_; 
v_tgt_1451_ = lean_ctor_get(v_x_1450_, 0);
v_b_1452_ = lean_ctor_get(v_x_1450_, 1);
v_i_1453_ = lean_ctor_get(v_x_1450_, 2);
v_ys_1454_ = lean_ctor_get(v_x_1450_, 3);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1456_ = v_x_1450_;
v_isShared_1457_ = v_isSharedCheck_1463_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_ys_1454_);
lean_inc(v_i_1453_);
lean_inc(v_b_1452_);
lean_inc(v_tgt_1451_);
lean_dec(v_x_1450_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1463_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
lean_inc_ref(v_f_1449_);
v___x_1458_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1452_);
v___x_1459_ = l_Lean_IR_MapVars_mapArgs(v_f_1449_, v_ys_1454_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 3, v___x_1459_);
lean_ctor_set(v___x_1456_, 1, v___x_1458_);
v___x_1461_ = v___x_1456_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_tgt_1451_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_i_1453_);
lean_ctor_set(v_reuseFailAlloc_1462_, 3, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
case 1:
{
lean_object* v_tgt_1464_; lean_object* v_b_1465_; lean_object* v_n_1466_; lean_object* v_x_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1476_; 
v_tgt_1464_ = lean_ctor_get(v_x_1450_, 0);
v_b_1465_ = lean_ctor_get(v_x_1450_, 1);
v_n_1466_ = lean_ctor_get(v_x_1450_, 2);
v_x_1467_ = lean_ctor_get(v_x_1450_, 3);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1469_ = v_x_1450_;
v_isShared_1470_ = v_isSharedCheck_1476_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_x_1467_);
lean_inc(v_n_1466_);
lean_inc(v_b_1465_);
lean_inc(v_tgt_1464_);
lean_dec(v_x_1450_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1476_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1474_; 
lean_inc_ref(v_f_1449_);
v___x_1471_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1465_);
v___x_1472_ = lean_apply_1(v_f_1449_, v_x_1467_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 3, v___x_1472_);
lean_ctor_set(v___x_1469_, 1, v___x_1471_);
v___x_1474_ = v___x_1469_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_tgt_1464_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_n_1466_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
case 2:
{
lean_object* v_tgt_1477_; lean_object* v_b_1478_; lean_object* v_x_1479_; lean_object* v_i_1480_; uint8_t v_updtHeader_1481_; lean_object* v_ys_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1492_; 
v_tgt_1477_ = lean_ctor_get(v_x_1450_, 0);
v_b_1478_ = lean_ctor_get(v_x_1450_, 1);
v_x_1479_ = lean_ctor_get(v_x_1450_, 2);
v_i_1480_ = lean_ctor_get(v_x_1450_, 3);
v_updtHeader_1481_ = lean_ctor_get_uint8(v_x_1450_, sizeof(void*)*5);
v_ys_1482_ = lean_ctor_get(v_x_1450_, 4);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1484_ = v_x_1450_;
v_isShared_1485_ = v_isSharedCheck_1492_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_ys_1482_);
lean_inc(v_i_1480_);
lean_inc(v_x_1479_);
lean_inc(v_b_1478_);
lean_inc(v_tgt_1477_);
lean_dec(v_x_1450_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1492_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1490_; 
lean_inc_ref_n(v_f_1449_, 2);
v___x_1486_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1478_);
v___x_1487_ = lean_apply_1(v_f_1449_, v_x_1479_);
v___x_1488_ = l_Lean_IR_MapVars_mapArgs(v_f_1449_, v_ys_1482_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 4, v___x_1488_);
lean_ctor_set(v___x_1484_, 2, v___x_1487_);
lean_ctor_set(v___x_1484_, 1, v___x_1486_);
v___x_1490_ = v___x_1484_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(2, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_tgt_1477_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1491_, 2, v___x_1487_);
lean_ctor_set(v_reuseFailAlloc_1491_, 3, v_i_1480_);
lean_ctor_set(v_reuseFailAlloc_1491_, 4, v___x_1488_);
lean_ctor_set_uint8(v_reuseFailAlloc_1491_, sizeof(void*)*5, v_updtHeader_1481_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
case 3:
{
lean_object* v_tgt_1493_; lean_object* v_b_1494_; lean_object* v_i_1495_; lean_object* v_x_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1505_; 
v_tgt_1493_ = lean_ctor_get(v_x_1450_, 0);
v_b_1494_ = lean_ctor_get(v_x_1450_, 1);
v_i_1495_ = lean_ctor_get(v_x_1450_, 2);
v_x_1496_ = lean_ctor_get(v_x_1450_, 3);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1498_ = v_x_1450_;
v_isShared_1499_ = v_isSharedCheck_1505_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_x_1496_);
lean_inc(v_i_1495_);
lean_inc(v_b_1494_);
lean_inc(v_tgt_1493_);
lean_dec(v_x_1450_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1505_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
lean_inc_ref(v_f_1449_);
v___x_1500_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1494_);
v___x_1501_ = lean_apply_1(v_f_1449_, v_x_1496_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 3, v___x_1501_);
lean_ctor_set(v___x_1498_, 1, v___x_1500_);
v___x_1503_ = v___x_1498_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_tgt_1493_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1504_, 2, v_i_1495_);
lean_ctor_set(v_reuseFailAlloc_1504_, 3, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
case 4:
{
lean_object* v_tgt_1506_; lean_object* v_b_1507_; lean_object* v_i_1508_; lean_object* v_x_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1518_; 
v_tgt_1506_ = lean_ctor_get(v_x_1450_, 0);
v_b_1507_ = lean_ctor_get(v_x_1450_, 1);
v_i_1508_ = lean_ctor_get(v_x_1450_, 2);
v_x_1509_ = lean_ctor_get(v_x_1450_, 3);
v_isSharedCheck_1518_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1511_ = v_x_1450_;
v_isShared_1512_ = v_isSharedCheck_1518_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_x_1509_);
lean_inc(v_i_1508_);
lean_inc(v_b_1507_);
lean_inc(v_tgt_1506_);
lean_dec(v_x_1450_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1518_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1516_; 
lean_inc_ref(v_f_1449_);
v___x_1513_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1507_);
v___x_1514_ = lean_apply_1(v_f_1449_, v_x_1509_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 3, v___x_1514_);
lean_ctor_set(v___x_1511_, 1, v___x_1513_);
v___x_1516_ = v___x_1511_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_tgt_1506_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_i_1508_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
case 5:
{
lean_object* v_tgt_1519_; lean_object* v_b_1520_; lean_object* v_ty_1521_; lean_object* v_n_1522_; lean_object* v_offset_1523_; lean_object* v_x_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1533_; 
v_tgt_1519_ = lean_ctor_get(v_x_1450_, 0);
v_b_1520_ = lean_ctor_get(v_x_1450_, 1);
v_ty_1521_ = lean_ctor_get(v_x_1450_, 2);
v_n_1522_ = lean_ctor_get(v_x_1450_, 3);
v_offset_1523_ = lean_ctor_get(v_x_1450_, 4);
v_x_1524_ = lean_ctor_get(v_x_1450_, 5);
v_isSharedCheck_1533_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1526_ = v_x_1450_;
v_isShared_1527_ = v_isSharedCheck_1533_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_x_1524_);
lean_inc(v_offset_1523_);
lean_inc(v_n_1522_);
lean_inc(v_ty_1521_);
lean_inc(v_b_1520_);
lean_inc(v_tgt_1519_);
lean_dec(v_x_1450_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1533_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
lean_inc_ref(v_f_1449_);
v___x_1528_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1520_);
v___x_1529_ = lean_apply_1(v_f_1449_, v_x_1524_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 5, v___x_1529_);
lean_ctor_set(v___x_1526_, 1, v___x_1528_);
v___x_1531_ = v___x_1526_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_tgt_1519_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1532_, 2, v_ty_1521_);
lean_ctor_set(v_reuseFailAlloc_1532_, 3, v_n_1522_);
lean_ctor_set(v_reuseFailAlloc_1532_, 4, v_offset_1523_);
lean_ctor_set(v_reuseFailAlloc_1532_, 5, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
case 6:
{
lean_object* v_tgt_1534_; lean_object* v_b_1535_; lean_object* v_ty_1536_; lean_object* v_c_1537_; lean_object* v_ys_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1547_; 
v_tgt_1534_ = lean_ctor_get(v_x_1450_, 0);
v_b_1535_ = lean_ctor_get(v_x_1450_, 1);
v_ty_1536_ = lean_ctor_get(v_x_1450_, 2);
v_c_1537_ = lean_ctor_get(v_x_1450_, 3);
v_ys_1538_ = lean_ctor_get(v_x_1450_, 4);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1540_ = v_x_1450_;
v_isShared_1541_ = v_isSharedCheck_1547_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_ys_1538_);
lean_inc(v_c_1537_);
lean_inc(v_ty_1536_);
lean_inc(v_b_1535_);
lean_inc(v_tgt_1534_);
lean_dec(v_x_1450_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1547_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; 
lean_inc_ref(v_f_1449_);
v___x_1542_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1535_);
v___x_1543_ = l_Lean_IR_MapVars_mapArgs(v_f_1449_, v_ys_1538_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 4, v___x_1543_);
lean_ctor_set(v___x_1540_, 1, v___x_1542_);
v___x_1545_ = v___x_1540_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(6, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_tgt_1534_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v_ty_1536_);
lean_ctor_set(v_reuseFailAlloc_1546_, 3, v_c_1537_);
lean_ctor_set(v_reuseFailAlloc_1546_, 4, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
case 7:
{
lean_object* v_tgt_1548_; lean_object* v_b_1549_; lean_object* v_c_1550_; lean_object* v_ys_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1560_; 
v_tgt_1548_ = lean_ctor_get(v_x_1450_, 0);
v_b_1549_ = lean_ctor_get(v_x_1450_, 1);
v_c_1550_ = lean_ctor_get(v_x_1450_, 2);
v_ys_1551_ = lean_ctor_get(v_x_1450_, 3);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1553_ = v_x_1450_;
v_isShared_1554_ = v_isSharedCheck_1560_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_ys_1551_);
lean_inc(v_c_1550_);
lean_inc(v_b_1549_);
lean_inc(v_tgt_1548_);
lean_dec(v_x_1450_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1560_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1558_; 
lean_inc_ref(v_f_1449_);
v___x_1555_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1549_);
v___x_1556_ = l_Lean_IR_MapVars_mapArgs(v_f_1449_, v_ys_1551_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 3, v___x_1556_);
lean_ctor_set(v___x_1553_, 1, v___x_1555_);
v___x_1558_ = v___x_1553_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_tgt_1548_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v___x_1555_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_c_1550_);
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
case 8:
{
lean_object* v_tgt_1561_; lean_object* v_b_1562_; lean_object* v_x_1563_; lean_object* v_ys_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1574_; 
v_tgt_1561_ = lean_ctor_get(v_x_1450_, 0);
v_b_1562_ = lean_ctor_get(v_x_1450_, 1);
v_x_1563_ = lean_ctor_get(v_x_1450_, 2);
v_ys_1564_ = lean_ctor_get(v_x_1450_, 3);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1566_ = v_x_1450_;
v_isShared_1567_ = v_isSharedCheck_1574_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_ys_1564_);
lean_inc(v_x_1563_);
lean_inc(v_b_1562_);
lean_inc(v_tgt_1561_);
lean_dec(v_x_1450_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1574_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1572_; 
lean_inc_ref_n(v_f_1449_, 2);
v___x_1568_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1562_);
v___x_1569_ = lean_apply_1(v_f_1449_, v_x_1563_);
v___x_1570_ = l_Lean_IR_MapVars_mapArgs(v_f_1449_, v_ys_1564_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 3, v___x_1570_);
lean_ctor_set(v___x_1566_, 2, v___x_1569_);
lean_ctor_set(v___x_1566_, 1, v___x_1568_);
v___x_1572_ = v___x_1566_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_tgt_1561_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1573_, 2, v___x_1569_);
lean_ctor_set(v_reuseFailAlloc_1573_, 3, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
case 9:
{
lean_object* v_tgt_1575_; lean_object* v_b_1576_; lean_object* v_ty_1577_; lean_object* v_x_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1587_; 
v_tgt_1575_ = lean_ctor_get(v_x_1450_, 0);
v_b_1576_ = lean_ctor_get(v_x_1450_, 1);
v_ty_1577_ = lean_ctor_get(v_x_1450_, 2);
v_x_1578_ = lean_ctor_get(v_x_1450_, 3);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1580_ = v_x_1450_;
v_isShared_1581_ = v_isSharedCheck_1587_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_x_1578_);
lean_inc(v_ty_1577_);
lean_inc(v_b_1576_);
lean_inc(v_tgt_1575_);
lean_dec(v_x_1450_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1587_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1585_; 
lean_inc_ref(v_f_1449_);
v___x_1582_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1576_);
v___x_1583_ = lean_apply_1(v_f_1449_, v_x_1578_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 3, v___x_1583_);
lean_ctor_set(v___x_1580_, 1, v___x_1582_);
v___x_1585_ = v___x_1580_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_tgt_1575_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1586_, 2, v_ty_1577_);
lean_ctor_set(v_reuseFailAlloc_1586_, 3, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
case 10:
{
lean_object* v_tgt_1588_; lean_object* v_b_1589_; lean_object* v_ty_1590_; lean_object* v_x_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1600_; 
v_tgt_1588_ = lean_ctor_get(v_x_1450_, 0);
v_b_1589_ = lean_ctor_get(v_x_1450_, 1);
v_ty_1590_ = lean_ctor_get(v_x_1450_, 2);
v_x_1591_ = lean_ctor_get(v_x_1450_, 3);
v_isSharedCheck_1600_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1593_ = v_x_1450_;
v_isShared_1594_ = v_isSharedCheck_1600_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_x_1591_);
lean_inc(v_ty_1590_);
lean_inc(v_b_1589_);
lean_inc(v_tgt_1588_);
lean_dec(v_x_1450_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1600_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
lean_inc_ref(v_f_1449_);
v___x_1595_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1589_);
v___x_1596_ = lean_apply_1(v_f_1449_, v_x_1591_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 3, v___x_1596_);
lean_ctor_set(v___x_1593_, 1, v___x_1595_);
v___x_1598_ = v___x_1593_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_tgt_1588_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1599_, 2, v_ty_1590_);
lean_ctor_set(v_reuseFailAlloc_1599_, 3, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
case 11:
{
lean_object* v_tgt_1601_; lean_object* v_b_1602_; uint8_t v_v_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1611_; 
v_tgt_1601_ = lean_ctor_get(v_x_1450_, 0);
v_b_1602_ = lean_ctor_get(v_x_1450_, 1);
v_v_1603_ = lean_ctor_get_uint8(v_x_1450_, sizeof(void*)*2);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1605_ = v_x_1450_;
v_isShared_1606_ = v_isSharedCheck_1611_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_b_1602_);
lean_inc(v_tgt_1601_);
lean_dec(v_x_1450_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1611_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1607_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1602_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 1, v___x_1607_);
v___x_1609_ = v___x_1605_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(11, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_tgt_1601_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v___x_1607_);
lean_ctor_set_uint8(v_reuseFailAlloc_1610_, sizeof(void*)*2, v_v_1603_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
case 12:
{
lean_object* v_tgt_1612_; lean_object* v_b_1613_; uint16_t v_v_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1622_; 
v_tgt_1612_ = lean_ctor_get(v_x_1450_, 0);
v_b_1613_ = lean_ctor_get(v_x_1450_, 1);
v_v_1614_ = lean_ctor_get_uint16(v_x_1450_, sizeof(void*)*2);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1616_ = v_x_1450_;
v_isShared_1617_ = v_isSharedCheck_1622_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_b_1613_);
lean_inc(v_tgt_1612_);
lean_dec(v_x_1450_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1622_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1618_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1613_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 1, v___x_1618_);
v___x_1620_ = v___x_1616_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(12, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_tgt_1612_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v___x_1618_);
lean_ctor_set_uint16(v_reuseFailAlloc_1621_, sizeof(void*)*2, v_v_1614_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
case 13:
{
lean_object* v_tgt_1623_; lean_object* v_b_1624_; uint32_t v_v_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1633_; 
v_tgt_1623_ = lean_ctor_get(v_x_1450_, 0);
v_b_1624_ = lean_ctor_get(v_x_1450_, 1);
v_v_1625_ = lean_ctor_get_uint32(v_x_1450_, sizeof(void*)*2);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1627_ = v_x_1450_;
v_isShared_1628_ = v_isSharedCheck_1633_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_b_1624_);
lean_inc(v_tgt_1623_);
lean_dec(v_x_1450_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1633_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1629_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1624_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 1, v___x_1629_);
v___x_1631_ = v___x_1627_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(13, 2, 4);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_tgt_1623_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v___x_1629_);
lean_ctor_set_uint32(v_reuseFailAlloc_1632_, sizeof(void*)*2, v_v_1625_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
case 14:
{
lean_object* v_tgt_1634_; lean_object* v_b_1635_; uint64_t v_v_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1644_; 
v_tgt_1634_ = lean_ctor_get(v_x_1450_, 0);
v_b_1635_ = lean_ctor_get(v_x_1450_, 1);
v_v_1636_ = lean_ctor_get_uint64(v_x_1450_, sizeof(void*)*2);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1638_ = v_x_1450_;
v_isShared_1639_ = v_isSharedCheck_1644_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_b_1635_);
lean_inc(v_tgt_1634_);
lean_dec(v_x_1450_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1644_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1640_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1635_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 1, v___x_1640_);
v___x_1642_ = v___x_1638_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(14, 2, 8);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_tgt_1634_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v___x_1640_);
lean_ctor_set_uint64(v_reuseFailAlloc_1643_, sizeof(void*)*2, v_v_1636_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
case 15:
{
lean_object* v_tgt_1645_; lean_object* v_b_1646_; uint64_t v_v_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1655_; 
v_tgt_1645_ = lean_ctor_get(v_x_1450_, 0);
v_b_1646_ = lean_ctor_get(v_x_1450_, 1);
v_v_1647_ = lean_ctor_get_uint64(v_x_1450_, sizeof(void*)*2);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1649_ = v_x_1450_;
v_isShared_1650_ = v_isSharedCheck_1655_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_b_1646_);
lean_inc(v_tgt_1645_);
lean_dec(v_x_1450_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1655_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1651_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1646_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 1, v___x_1651_);
v___x_1653_ = v___x_1649_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(15, 2, 8);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_tgt_1645_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v___x_1651_);
lean_ctor_set_uint64(v_reuseFailAlloc_1654_, sizeof(void*)*2, v_v_1647_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
case 16:
{
lean_object* v_tgt_1656_; lean_object* v_b_1657_; lean_object* v_v_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1666_; 
v_tgt_1656_ = lean_ctor_get(v_x_1450_, 0);
v_b_1657_ = lean_ctor_get(v_x_1450_, 1);
v_v_1658_ = lean_ctor_get(v_x_1450_, 2);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1660_ = v_x_1450_;
v_isShared_1661_ = v_isSharedCheck_1666_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_v_1658_);
lean_inc(v_b_1657_);
lean_inc(v_tgt_1656_);
lean_dec(v_x_1450_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1666_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1662_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1657_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 1, v___x_1662_);
v___x_1664_ = v___x_1660_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_tgt_1656_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v_v_1658_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
case 17:
{
lean_object* v_tgt_1667_; lean_object* v_b_1668_; lean_object* v_v_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1677_; 
v_tgt_1667_ = lean_ctor_get(v_x_1450_, 0);
v_b_1668_ = lean_ctor_get(v_x_1450_, 1);
v_v_1669_ = lean_ctor_get(v_x_1450_, 2);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1671_ = v_x_1450_;
v_isShared_1672_ = v_isSharedCheck_1677_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_v_1669_);
lean_inc(v_b_1668_);
lean_inc(v_tgt_1667_);
lean_dec(v_x_1450_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1677_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1673_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1668_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 1, v___x_1673_);
v___x_1675_ = v___x_1671_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(17, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_tgt_1667_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1676_, 2, v_v_1669_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
case 18:
{
lean_object* v_tgt_1678_; lean_object* v_b_1679_; lean_object* v_x_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1689_; 
v_tgt_1678_ = lean_ctor_get(v_x_1450_, 0);
v_b_1679_ = lean_ctor_get(v_x_1450_, 1);
v_x_1680_ = lean_ctor_get(v_x_1450_, 2);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1682_ = v_x_1450_;
v_isShared_1683_ = v_isSharedCheck_1689_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_x_1680_);
lean_inc(v_b_1679_);
lean_inc(v_tgt_1678_);
lean_dec(v_x_1450_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1689_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1687_; 
lean_inc_ref(v_f_1449_);
v___x_1684_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1679_);
v___x_1685_ = lean_apply_1(v_f_1449_, v_x_1680_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 2, v___x_1685_);
lean_ctor_set(v___x_1682_, 1, v___x_1684_);
v___x_1687_ = v___x_1682_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(18, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_tgt_1678_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1688_, 2, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
case 19:
{
lean_object* v_j_1690_; lean_object* v_xs_1691_; lean_object* v_v_1692_; lean_object* v_b_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1702_; 
v_j_1690_ = lean_ctor_get(v_x_1450_, 0);
v_xs_1691_ = lean_ctor_get(v_x_1450_, 1);
v_v_1692_ = lean_ctor_get(v_x_1450_, 2);
v_b_1693_ = lean_ctor_get(v_x_1450_, 3);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1695_ = v_x_1450_;
v_isShared_1696_ = v_isSharedCheck_1702_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_b_1693_);
lean_inc(v_v_1692_);
lean_inc(v_xs_1691_);
lean_inc(v_j_1690_);
lean_dec(v_x_1450_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1702_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1700_; 
lean_inc_ref(v_f_1449_);
v___x_1697_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_v_1692_);
v___x_1698_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1693_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 3, v___x_1698_);
lean_ctor_set(v___x_1695_, 2, v___x_1697_);
v___x_1700_ = v___x_1695_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(19, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_j_1690_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_xs_1691_);
lean_ctor_set(v_reuseFailAlloc_1701_, 2, v___x_1697_);
lean_ctor_set(v_reuseFailAlloc_1701_, 3, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
case 20:
{
lean_object* v_x_1703_; lean_object* v_i_1704_; lean_object* v_y_1705_; lean_object* v_b_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1726_; 
v_x_1703_ = lean_ctor_get(v_x_1450_, 0);
v_i_1704_ = lean_ctor_get(v_x_1450_, 1);
v_y_1705_ = lean_ctor_get(v_x_1450_, 2);
v_b_1706_ = lean_ctor_get(v_x_1450_, 3);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1708_ = v_x_1450_;
v_isShared_1709_ = v_isSharedCheck_1726_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_b_1706_);
lean_inc(v_y_1705_);
lean_inc(v_i_1704_);
lean_inc(v_x_1703_);
lean_dec(v_x_1450_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1726_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v___y_1712_; 
lean_inc_ref(v_f_1449_);
v___x_1710_ = lean_apply_1(v_f_1449_, v_x_1703_);
if (lean_obj_tag(v_y_1705_) == 0)
{
lean_object* v_id_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1725_; 
v_id_1717_ = lean_ctor_get(v_y_1705_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_y_1705_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1719_ = v_y_1705_;
v_isShared_1720_ = v_isSharedCheck_1725_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_id_1717_);
lean_dec(v_y_1705_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1725_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1723_; 
lean_inc_ref(v_f_1449_);
v___x_1721_ = lean_apply_1(v_f_1449_, v_id_1717_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1721_);
v___x_1723_ = v___x_1719_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
v___y_1712_ = v___x_1723_;
goto v___jp_1711_;
}
}
}
else
{
v___y_1712_ = v_y_1705_;
goto v___jp_1711_;
}
v___jp_1711_:
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1713_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1706_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 3, v___x_1713_);
lean_ctor_set(v___x_1708_, 2, v___y_1712_);
lean_ctor_set(v___x_1708_, 0, v___x_1710_);
v___x_1715_ = v___x_1708_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(20, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_i_1704_);
lean_ctor_set(v_reuseFailAlloc_1716_, 2, v___y_1712_);
lean_ctor_set(v_reuseFailAlloc_1716_, 3, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
case 21:
{
lean_object* v_x_1727_; lean_object* v_cidx_1728_; lean_object* v_b_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1738_; 
v_x_1727_ = lean_ctor_get(v_x_1450_, 0);
v_cidx_1728_ = lean_ctor_get(v_x_1450_, 1);
v_b_1729_ = lean_ctor_get(v_x_1450_, 2);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1731_ = v_x_1450_;
v_isShared_1732_ = v_isSharedCheck_1738_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_b_1729_);
lean_inc(v_cidx_1728_);
lean_inc(v_x_1727_);
lean_dec(v_x_1450_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1738_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
lean_inc_ref(v_f_1449_);
v___x_1733_ = lean_apply_1(v_f_1449_, v_x_1727_);
v___x_1734_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1729_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 2, v___x_1734_);
lean_ctor_set(v___x_1731_, 0, v___x_1733_);
v___x_1736_ = v___x_1731_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(21, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1733_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v_cidx_1728_);
lean_ctor_set(v_reuseFailAlloc_1737_, 2, v___x_1734_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
case 22:
{
lean_object* v_x_1739_; lean_object* v_i_1740_; lean_object* v_y_1741_; lean_object* v_b_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1752_; 
v_x_1739_ = lean_ctor_get(v_x_1450_, 0);
v_i_1740_ = lean_ctor_get(v_x_1450_, 1);
v_y_1741_ = lean_ctor_get(v_x_1450_, 2);
v_b_1742_ = lean_ctor_get(v_x_1450_, 3);
v_isSharedCheck_1752_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1744_ = v_x_1450_;
v_isShared_1745_ = v_isSharedCheck_1752_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_b_1742_);
lean_inc(v_y_1741_);
lean_inc(v_i_1740_);
lean_inc(v_x_1739_);
lean_dec(v_x_1450_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1752_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1750_; 
lean_inc_ref_n(v_f_1449_, 2);
v___x_1746_ = lean_apply_1(v_f_1449_, v_x_1739_);
v___x_1747_ = lean_apply_1(v_f_1449_, v_y_1741_);
v___x_1748_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1742_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 3, v___x_1748_);
lean_ctor_set(v___x_1744_, 2, v___x_1747_);
lean_ctor_set(v___x_1744_, 0, v___x_1746_);
v___x_1750_ = v___x_1744_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(22, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1746_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_i_1740_);
lean_ctor_set(v_reuseFailAlloc_1751_, 2, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1751_, 3, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
case 23:
{
lean_object* v_x_1753_; lean_object* v_i_1754_; lean_object* v_offset_1755_; lean_object* v_y_1756_; lean_object* v_ty_1757_; lean_object* v_b_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1768_; 
v_x_1753_ = lean_ctor_get(v_x_1450_, 0);
v_i_1754_ = lean_ctor_get(v_x_1450_, 1);
v_offset_1755_ = lean_ctor_get(v_x_1450_, 2);
v_y_1756_ = lean_ctor_get(v_x_1450_, 3);
v_ty_1757_ = lean_ctor_get(v_x_1450_, 4);
v_b_1758_ = lean_ctor_get(v_x_1450_, 5);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1760_ = v_x_1450_;
v_isShared_1761_ = v_isSharedCheck_1768_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_b_1758_);
lean_inc(v_ty_1757_);
lean_inc(v_y_1756_);
lean_inc(v_offset_1755_);
lean_inc(v_i_1754_);
lean_inc(v_x_1753_);
lean_dec(v_x_1450_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1768_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
lean_inc_ref_n(v_f_1449_, 2);
v___x_1762_ = lean_apply_1(v_f_1449_, v_x_1753_);
v___x_1763_ = lean_apply_1(v_f_1449_, v_y_1756_);
v___x_1764_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1758_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 5, v___x_1764_);
lean_ctor_set(v___x_1760_, 3, v___x_1763_);
lean_ctor_set(v___x_1760_, 0, v___x_1762_);
v___x_1766_ = v___x_1760_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(23, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1762_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_i_1754_);
lean_ctor_set(v_reuseFailAlloc_1767_, 2, v_offset_1755_);
lean_ctor_set(v_reuseFailAlloc_1767_, 3, v___x_1763_);
lean_ctor_set(v_reuseFailAlloc_1767_, 4, v_ty_1757_);
lean_ctor_set(v_reuseFailAlloc_1767_, 5, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
case 24:
{
lean_object* v_x_1769_; lean_object* v_n_1770_; uint8_t v_c_1771_; uint8_t v_persistent_1772_; lean_object* v_b_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1782_; 
v_x_1769_ = lean_ctor_get(v_x_1450_, 0);
v_n_1770_ = lean_ctor_get(v_x_1450_, 1);
v_c_1771_ = lean_ctor_get_uint8(v_x_1450_, sizeof(void*)*3);
v_persistent_1772_ = lean_ctor_get_uint8(v_x_1450_, sizeof(void*)*3 + 1);
v_b_1773_ = lean_ctor_get(v_x_1450_, 2);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1775_ = v_x_1450_;
v_isShared_1776_ = v_isSharedCheck_1782_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_b_1773_);
lean_inc(v_n_1770_);
lean_inc(v_x_1769_);
lean_dec(v_x_1450_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1782_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1780_; 
lean_inc_ref(v_f_1449_);
v___x_1777_ = lean_apply_1(v_f_1449_, v_x_1769_);
v___x_1778_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1773_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 2, v___x_1778_);
lean_ctor_set(v___x_1775_, 0, v___x_1777_);
v___x_1780_ = v___x_1775_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(24, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_n_1770_);
lean_ctor_set(v_reuseFailAlloc_1781_, 2, v___x_1778_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, sizeof(void*)*3, v_c_1771_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, sizeof(void*)*3 + 1, v_persistent_1772_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
case 25:
{
lean_object* v_x_1783_; lean_object* v_n_1784_; uint8_t v_c_1785_; uint8_t v_persistent_1786_; lean_object* v_b_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1796_; 
v_x_1783_ = lean_ctor_get(v_x_1450_, 0);
v_n_1784_ = lean_ctor_get(v_x_1450_, 1);
v_c_1785_ = lean_ctor_get_uint8(v_x_1450_, sizeof(void*)*3);
v_persistent_1786_ = lean_ctor_get_uint8(v_x_1450_, sizeof(void*)*3 + 1);
v_b_1787_ = lean_ctor_get(v_x_1450_, 2);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1789_ = v_x_1450_;
v_isShared_1790_ = v_isSharedCheck_1796_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_b_1787_);
lean_inc(v_n_1784_);
lean_inc(v_x_1783_);
lean_dec(v_x_1450_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1796_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1794_; 
lean_inc_ref(v_f_1449_);
v___x_1791_ = lean_apply_1(v_f_1449_, v_x_1783_);
v___x_1792_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1787_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 2, v___x_1792_);
lean_ctor_set(v___x_1789_, 0, v___x_1791_);
v___x_1794_ = v___x_1789_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(25, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1791_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_n_1784_);
lean_ctor_set(v_reuseFailAlloc_1795_, 2, v___x_1792_);
lean_ctor_set_uint8(v_reuseFailAlloc_1795_, sizeof(void*)*3, v_c_1785_);
lean_ctor_set_uint8(v_reuseFailAlloc_1795_, sizeof(void*)*3 + 1, v_persistent_1786_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
case 26:
{
lean_object* v_x_1797_; lean_object* v_b_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1807_; 
v_x_1797_ = lean_ctor_get(v_x_1450_, 0);
v_b_1798_ = lean_ctor_get(v_x_1450_, 1);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1800_ = v_x_1450_;
v_isShared_1801_ = v_isSharedCheck_1807_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_b_1798_);
lean_inc(v_x_1797_);
lean_dec(v_x_1450_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1807_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
lean_inc_ref(v_f_1449_);
v___x_1802_ = lean_apply_1(v_f_1449_, v_x_1797_);
v___x_1803_ = l_Lean_IR_MapVars_mapFnBody(v_f_1449_, v_b_1798_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 1, v___x_1803_);
lean_ctor_set(v___x_1800_, 0, v___x_1802_);
v___x_1805_ = v___x_1800_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(26, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
case 27:
{
lean_object* v_tid_1808_; lean_object* v_x_1809_; lean_object* v_xType_1810_; lean_object* v_cs_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1822_; 
v_tid_1808_ = lean_ctor_get(v_x_1450_, 0);
v_x_1809_ = lean_ctor_get(v_x_1450_, 1);
v_xType_1810_ = lean_ctor_get(v_x_1450_, 2);
v_cs_1811_ = lean_ctor_get(v_x_1450_, 3);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1813_ = v_x_1450_;
v_isShared_1814_ = v_isSharedCheck_1822_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_cs_1811_);
lean_inc(v_xType_1810_);
lean_inc(v_x_1809_);
lean_inc(v_tid_1808_);
lean_dec(v_x_1450_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1822_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; size_t v_sz_1816_; size_t v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1820_; 
lean_inc_ref(v_f_1449_);
v___x_1815_ = lean_apply_1(v_f_1449_, v_x_1809_);
v_sz_1816_ = lean_array_size(v_cs_1811_);
v___x_1817_ = ((size_t)0ULL);
v___x_1818_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(v_f_1449_, v_sz_1816_, v___x_1817_, v_cs_1811_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 3, v___x_1818_);
lean_ctor_set(v___x_1813_, 1, v___x_1815_);
v___x_1820_ = v___x_1813_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(27, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_tid_1808_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v___x_1815_);
lean_ctor_set(v_reuseFailAlloc_1821_, 2, v_xType_1810_);
lean_ctor_set(v_reuseFailAlloc_1821_, 3, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
case 28:
{
lean_object* v_x_1823_; 
v_x_1823_ = lean_ctor_get(v_x_1450_, 0);
lean_inc(v_x_1823_);
if (lean_obj_tag(v_x_1823_) == 0)
{
lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1839_; 
v_isSharedCheck_1839_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1839_ == 0)
{
lean_object* v_unused_1840_; 
v_unused_1840_ = lean_ctor_get(v_x_1450_, 0);
lean_dec(v_unused_1840_);
v___x_1825_ = v_x_1450_;
v_isShared_1826_ = v_isSharedCheck_1839_;
goto v_resetjp_1824_;
}
else
{
lean_dec(v_x_1450_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1839_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v_id_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1838_; 
v_id_1827_ = lean_ctor_get(v_x_1823_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_x_1823_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1829_ = v_x_1823_;
v_isShared_1830_ = v_isSharedCheck_1838_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_id_1827_);
lean_dec(v_x_1823_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1838_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1831_ = lean_apply_1(v_f_1449_, v_id_1827_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1831_);
v___x_1833_ = v___x_1829_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_object* v___x_1835_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1833_);
v___x_1835_ = v___x_1825_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(28, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_1449_);
return v_x_1450_;
}
}
case 29:
{
lean_object* v_j_1841_; lean_object* v_ys_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1850_; 
v_j_1841_ = lean_ctor_get(v_x_1450_, 0);
v_ys_1842_ = lean_ctor_get(v_x_1450_, 1);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1844_ = v_x_1450_;
v_isShared_1845_ = v_isSharedCheck_1850_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_ys_1842_);
lean_inc(v_j_1841_);
lean_dec(v_x_1450_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1850_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1846_ = l_Lean_IR_MapVars_mapArgs(v_f_1449_, v_ys_1842_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 1, v___x_1846_);
v___x_1848_ = v___x_1844_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(29, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_j_1841_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
default: 
{
lean_dec_ref(v_f_1449_);
return v_x_1450_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(lean_object* v_f_1851_, size_t v_sz_1852_, size_t v_i_1853_, lean_object* v_bs_1854_){
_start:
{
uint8_t v___x_1855_; 
v___x_1855_ = lean_usize_dec_lt(v_i_1853_, v_sz_1852_);
if (v___x_1855_ == 0)
{
lean_dec_ref(v_f_1851_);
return v_bs_1854_;
}
else
{
lean_object* v_v_1856_; lean_object* v___x_1857_; lean_object* v_bs_x27_1858_; lean_object* v___y_1860_; 
v_v_1856_ = lean_array_uget(v_bs_1854_, v_i_1853_);
v___x_1857_ = lean_unsigned_to_nat(0u);
v_bs_x27_1858_ = lean_array_uset(v_bs_1854_, v_i_1853_, v___x_1857_);
if (lean_obj_tag(v_v_1856_) == 0)
{
lean_object* v_info_1865_; lean_object* v_b_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1874_; 
v_info_1865_ = lean_ctor_get(v_v_1856_, 0);
v_b_1866_ = lean_ctor_get(v_v_1856_, 1);
v_isSharedCheck_1874_ = !lean_is_exclusive(v_v_1856_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1868_ = v_v_1856_;
v_isShared_1869_ = v_isSharedCheck_1874_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_b_1866_);
lean_inc(v_info_1865_);
lean_dec(v_v_1856_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1874_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
lean_inc_ref(v_f_1851_);
v___x_1870_ = l_Lean_IR_MapVars_mapFnBody(v_f_1851_, v_b_1866_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 1, v___x_1870_);
v___x_1872_ = v___x_1868_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_info_1865_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
v___y_1860_ = v___x_1872_;
goto v___jp_1859_;
}
}
}
else
{
lean_object* v_b_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1883_; 
v_b_1875_ = lean_ctor_get(v_v_1856_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v_v_1856_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1877_ = v_v_1856_;
v_isShared_1878_ = v_isSharedCheck_1883_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_b_1875_);
lean_dec(v_v_1856_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1883_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; lean_object* v___x_1881_; 
lean_inc_ref(v_f_1851_);
v___x_1879_ = l_Lean_IR_MapVars_mapFnBody(v_f_1851_, v_b_1875_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1879_);
v___x_1881_ = v___x_1877_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
v___y_1860_ = v___x_1881_;
goto v___jp_1859_;
}
}
}
v___jp_1859_:
{
size_t v___x_1861_; size_t v___x_1862_; lean_object* v___x_1863_; 
v___x_1861_ = ((size_t)1ULL);
v___x_1862_ = lean_usize_add(v_i_1853_, v___x_1861_);
v___x_1863_ = lean_array_uset(v_bs_x27_1858_, v_i_1853_, v___y_1860_);
v_i_1853_ = v___x_1862_;
v_bs_1854_ = v___x_1863_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0___boxed(lean_object* v_f_1884_, lean_object* v_sz_1885_, lean_object* v_i_1886_, lean_object* v_bs_1887_){
_start:
{
size_t v_sz_boxed_1888_; size_t v_i_boxed_1889_; lean_object* v_res_1890_; 
v_sz_boxed_1888_ = lean_unbox_usize(v_sz_1885_);
lean_dec(v_sz_1885_);
v_i_boxed_1889_ = lean_unbox_usize(v_i_1886_);
lean_dec(v_i_1886_);
v_res_1890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_MapVars_mapFnBody_spec__0(v_f_1884_, v_sz_boxed_1888_, v_i_boxed_1889_, v_bs_1887_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_mapVars(lean_object* v_f_1891_, lean_object* v_b_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_IR_MapVars_mapFnBody(v_f_1891_, v_b_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lam__0(lean_object* v_x_1894_, lean_object* v_y_1895_, lean_object* v_z_1896_){
_start:
{
uint8_t v___x_1897_; 
v___x_1897_ = l_Lean_IR_instBEqVarId_beq(v_x_1894_, v_z_1896_);
if (v___x_1897_ == 0)
{
lean_inc(v_z_1896_);
return v_z_1896_;
}
else
{
lean_inc(v_y_1895_);
return v_y_1895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lam__0___boxed(lean_object* v_x_1898_, lean_object* v_y_1899_, lean_object* v_z_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_IR_FnBody_replaceVar___lam__0(v_x_1898_, v_y_1899_, v_z_1900_);
lean_dec(v_z_1900_);
lean_dec(v_y_1899_);
lean_dec(v_x_1898_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar(lean_object* v_x_1902_, lean_object* v_y_1903_, lean_object* v_b_1904_){
_start:
{
lean_object* v___f_1905_; lean_object* v___x_1906_; 
v___f_1905_ = lean_alloc_closure((void*)(l_Lean_IR_FnBody_replaceVar___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1905_, 0, v_x_1902_);
lean_closure_set(v___f_1905_, 1, v_y_1903_);
v___x_1906_ = l_Lean_IR_MapVars_mapFnBody(v___f_1905_, v_b_1904_);
return v___x_1906_;
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
