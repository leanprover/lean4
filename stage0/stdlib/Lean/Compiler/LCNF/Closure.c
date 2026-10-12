// Lean compiler output
// Module: Lean.Compiler.LCNF.Closure
// Imports: public import Lean.Util.ForEachExprWhere public import Lean.Compiler.LCNF.CompilerM
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
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_mod(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
extern lean_object* l_Lean_ForEachExprWhere_initCache;
lean_object* lean_st_mk_ref(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_markVisited___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_markVisited___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_markVisited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_markVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__1 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__2 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__3 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__4 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Closure_collectType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isFVar___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Closure_collectType___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Closure_collectType___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Compiler.LCNF.Closure.collectFVar"};
static const lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_Closure_collectFVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Compiler.LCNF.Closure"};
static const lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Closure_collectFVar___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_Closure_run___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Closure_run___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Closure_run___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
return v_x_1_;
}
else
{
lean_object* v_key_3_; lean_object* v_value_4_; lean_object* v_tail_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_28_; 
v_key_3_ = lean_ctor_get(v_x_2_, 0);
v_value_4_ = lean_ctor_get(v_x_2_, 1);
v_tail_5_ = lean_ctor_get(v_x_2_, 2);
v_isSharedCheck_28_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_28_ == 0)
{
v___x_7_ = v_x_2_;
v_isShared_8_ = v_isSharedCheck_28_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_tail_5_);
lean_inc(v_value_4_);
lean_inc(v_key_3_);
lean_dec(v_x_2_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_28_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; uint64_t v___x_10_; uint64_t v___x_11_; uint64_t v___x_12_; uint64_t v_fold_13_; uint64_t v___x_14_; uint64_t v___x_15_; uint64_t v___x_16_; size_t v___x_17_; size_t v___x_18_; size_t v___x_19_; size_t v___x_20_; size_t v___x_21_; lean_object* v___x_22_; lean_object* v___x_24_; 
v___x_9_ = lean_array_get_size(v_x_1_);
v___x_10_ = l_Lean_instHashableFVarId_hash(v_key_3_);
v___x_11_ = 32ULL;
v___x_12_ = lean_uint64_shift_right(v___x_10_, v___x_11_);
v_fold_13_ = lean_uint64_xor(v___x_10_, v___x_12_);
v___x_14_ = 16ULL;
v___x_15_ = lean_uint64_shift_right(v_fold_13_, v___x_14_);
v___x_16_ = lean_uint64_xor(v_fold_13_, v___x_15_);
v___x_17_ = lean_uint64_to_usize(v___x_16_);
v___x_18_ = lean_usize_of_nat(v___x_9_);
v___x_19_ = ((size_t)1ULL);
v___x_20_ = lean_usize_sub(v___x_18_, v___x_19_);
v___x_21_ = lean_usize_land(v___x_17_, v___x_20_);
v___x_22_ = lean_array_uget_borrowed(v_x_1_, v___x_21_);
lean_inc(v___x_22_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 2, v___x_22_);
v___x_24_ = v___x_7_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_key_3_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v_value_4_);
lean_ctor_set(v_reuseFailAlloc_27_, 2, v___x_22_);
v___x_24_ = v_reuseFailAlloc_27_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
lean_object* v___x_25_; 
v___x_25_ = lean_array_uset(v_x_1_, v___x_21_, v___x_24_);
v_x_1_ = v___x_25_;
v_x_2_ = v_tail_5_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2___redArg(lean_object* v_i_29_, lean_object* v_source_30_, lean_object* v_target_31_){
_start:
{
lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_32_ = lean_array_get_size(v_source_30_);
v___x_33_ = lean_nat_dec_lt(v_i_29_, v___x_32_);
if (v___x_33_ == 0)
{
lean_dec_ref(v_source_30_);
lean_dec(v_i_29_);
return v_target_31_;
}
else
{
lean_object* v_es_34_; lean_object* v___x_35_; lean_object* v_source_36_; lean_object* v_target_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v_es_34_ = lean_array_fget(v_source_30_, v_i_29_);
v___x_35_ = lean_box(0);
v_source_36_ = lean_array_fset(v_source_30_, v_i_29_, v___x_35_);
v_target_37_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2_spec__3___redArg(v_target_31_, v_es_34_);
v___x_38_ = lean_unsigned_to_nat(1u);
v___x_39_ = lean_nat_add(v_i_29_, v___x_38_);
lean_dec(v_i_29_);
v_i_29_ = v___x_39_;
v_source_30_ = v_source_36_;
v_target_31_ = v_target_37_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1___redArg(lean_object* v_data_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_nbuckets_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_42_ = lean_array_get_size(v_data_41_);
v___x_43_ = lean_unsigned_to_nat(2u);
v_nbuckets_44_ = lean_nat_mul(v___x_42_, v___x_43_);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_box(0);
v___x_47_ = lean_mk_array(v_nbuckets_44_, v___x_46_);
v___x_48_ = lean_array_propagate_mark(v_data_41_, v___x_47_);
v___x_49_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2___redArg(v___x_45_, v_data_41_, v___x_48_);
return v___x_49_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg(lean_object* v_a_50_, lean_object* v_x_51_){
_start:
{
if (lean_obj_tag(v_x_51_) == 0)
{
uint8_t v___x_52_; 
v___x_52_ = 0;
return v___x_52_;
}
else
{
lean_object* v_key_53_; lean_object* v_tail_54_; uint8_t v___x_55_; 
v_key_53_ = lean_ctor_get(v_x_51_, 0);
v_tail_54_ = lean_ctor_get(v_x_51_, 2);
v___x_55_ = l_Lean_instBEqFVarId_beq(v_key_53_, v_a_50_);
if (v___x_55_ == 0)
{
v_x_51_ = v_tail_54_;
goto _start;
}
else
{
return v___x_55_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_50_ = stack[0].m_obj;
lean_object* v_x_51_ = stack[1].m_obj;
uint8_t v_res_57_;
v_res_57_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg(v_a_50_, v_x_51_);
stack->m_num = v_res_57_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg___boxed(lean_object* v_a_58_, lean_object* v_x_59_){
_start:
{
uint8_t v_res_60_; lean_object* v_r_61_; 
v_res_60_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg(v_a_58_, v_x_59_);
lean_dec(v_x_59_);
lean_dec(v_a_58_);
v_r_61_ = lean_box(v_res_60_);
return v_r_61_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0___redArg(lean_object* v_m_62_, lean_object* v_a_63_, lean_object* v_b_64_){
_start:
{
lean_object* v_size_65_; lean_object* v_buckets_66_; lean_object* v___x_67_; uint64_t v___x_68_; uint64_t v___x_69_; uint64_t v___x_70_; uint64_t v_fold_71_; uint64_t v___x_72_; uint64_t v___x_73_; uint64_t v___x_74_; size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; size_t v___x_78_; size_t v___x_79_; lean_object* v_bkt_80_; uint8_t v___x_81_; 
v_size_65_ = lean_ctor_get(v_m_62_, 0);
v_buckets_66_ = lean_ctor_get(v_m_62_, 1);
v___x_67_ = lean_array_get_size(v_buckets_66_);
v___x_68_ = l_Lean_instHashableFVarId_hash(v_a_63_);
v___x_69_ = 32ULL;
v___x_70_ = lean_uint64_shift_right(v___x_68_, v___x_69_);
v_fold_71_ = lean_uint64_xor(v___x_68_, v___x_70_);
v___x_72_ = 16ULL;
v___x_73_ = lean_uint64_shift_right(v_fold_71_, v___x_72_);
v___x_74_ = lean_uint64_xor(v_fold_71_, v___x_73_);
v___x_75_ = lean_uint64_to_usize(v___x_74_);
v___x_76_ = lean_usize_of_nat(v___x_67_);
v___x_77_ = ((size_t)1ULL);
v___x_78_ = lean_usize_sub(v___x_76_, v___x_77_);
v___x_79_ = lean_usize_land(v___x_75_, v___x_78_);
v_bkt_80_ = lean_array_uget_borrowed(v_buckets_66_, v___x_79_);
v___x_81_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg(v_a_63_, v_bkt_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_102_; 
lean_inc_ref(v_buckets_66_);
lean_inc(v_size_65_);
v_isSharedCheck_102_ = !lean_is_exclusive(v_m_62_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; lean_object* v_unused_104_; 
v_unused_103_ = lean_ctor_get(v_m_62_, 1);
lean_dec(v_unused_103_);
v_unused_104_ = lean_ctor_get(v_m_62_, 0);
lean_dec(v_unused_104_);
v___x_83_ = v_m_62_;
v_isShared_84_ = v_isSharedCheck_102_;
goto v_resetjp_82_;
}
else
{
lean_dec(v_m_62_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_102_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; lean_object* v_size_x27_86_; lean_object* v___x_87_; lean_object* v_buckets_x27_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_85_ = lean_unsigned_to_nat(1u);
v_size_x27_86_ = lean_nat_add(v_size_65_, v___x_85_);
lean_dec(v_size_65_);
lean_inc(v_bkt_80_);
v___x_87_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_87_, 0, v_a_63_);
lean_ctor_set(v___x_87_, 1, v_b_64_);
lean_ctor_set(v___x_87_, 2, v_bkt_80_);
v_buckets_x27_88_ = lean_array_uset(v_buckets_66_, v___x_79_, v___x_87_);
v___x_89_ = lean_unsigned_to_nat(4u);
v___x_90_ = lean_nat_mul(v_size_x27_86_, v___x_89_);
v___x_91_ = lean_unsigned_to_nat(3u);
v___x_92_ = lean_nat_div(v___x_90_, v___x_91_);
lean_dec(v___x_90_);
v___x_93_ = lean_array_get_size(v_buckets_x27_88_);
v___x_94_ = lean_nat_dec_le(v___x_92_, v___x_93_);
lean_dec(v___x_92_);
if (v___x_94_ == 0)
{
lean_object* v_val_95_; lean_object* v___x_97_; 
v_val_95_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1___redArg(v_buckets_x27_88_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v_val_95_);
lean_ctor_set(v___x_83_, 0, v_size_x27_86_);
v___x_97_ = v___x_83_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_size_x27_86_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v_val_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
else
{
lean_object* v___x_100_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v_buckets_x27_88_);
lean_ctor_set(v___x_83_, 0, v_size_x27_86_);
v___x_100_ = v___x_83_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_size_x27_86_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_buckets_x27_88_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
else
{
lean_dec(v_b_64_);
lean_dec(v_a_63_);
return v_m_62_;
}
}
}
lean_object* l_Lean_Compiler_LCNF_Closure_markVisited___redArg(lean_object* v_fvarId_105_, lean_object* v_a_106_){
_start:
{
lean_object* v___x_108_; lean_object* v_visited_109_; lean_object* v_params_110_; lean_object* v_decls_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_122_; 
v___x_108_ = lean_st_ref_take(v_a_106_);
v_visited_109_ = lean_ctor_get(v___x_108_, 0);
v_params_110_ = lean_ctor_get(v___x_108_, 1);
v_decls_111_ = lean_ctor_get(v___x_108_, 2);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_122_ == 0)
{
v___x_113_ = v___x_108_;
v_isShared_114_ = v_isSharedCheck_122_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_decls_111_);
lean_inc(v_params_110_);
lean_inc(v_visited_109_);
lean_dec(v___x_108_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_122_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_118_; 
v___x_115_ = lean_box(0);
v___x_116_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0___redArg(v_visited_109_, v_fvarId_105_, v___x_115_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_116_);
v___x_118_ = v___x_113_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_params_110_);
lean_ctor_set(v_reuseFailAlloc_121_, 2, v_decls_111_);
v___x_118_ = v_reuseFailAlloc_121_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_st_ref_put(v_a_106_, v___x_118_);
v___x_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_115_);
return v___x_120_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Closure_markVisited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_105_ = stack[0].m_obj;
lean_object* v_a_106_ = stack[1].m_obj;
lean_object* v_res_123_;
v_res_123_ = l_Lean_Compiler_LCNF_Closure_markVisited___redArg(v_fvarId_105_, v_a_106_);
stack->m_obj
 = v_res_123_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_markVisited___redArg___boxed(lean_object* v_fvarId_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Compiler_LCNF_Closure_markVisited___redArg(v_fvarId_124_, v_a_125_);
lean_dec(v_a_125_);
return v_res_127_;
}
}
lean_object* l_Lean_Compiler_LCNF_Closure_markVisited(lean_object* v_fvarId_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Compiler_LCNF_Closure_markVisited___redArg(v_fvarId_128_, v_a_130_);
return v___x_136_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Closure_markVisited_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_128_ = stack[0].m_obj;
lean_object* v_a_129_ = stack[1].m_obj;
lean_object* v_a_130_ = stack[2].m_obj;
lean_object* v_a_131_ = stack[3].m_obj;
lean_object* v_a_132_ = stack[4].m_obj;
lean_object* v_a_133_ = stack[5].m_obj;
lean_object* v_a_134_ = stack[6].m_obj;
lean_object* v_res_137_;
v_res_137_ = l_Lean_Compiler_LCNF_Closure_markVisited(v_fvarId_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_);
stack->m_obj
 = v_res_137_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_markVisited___boxed(lean_object* v_fvarId_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Compiler_LCNF_Closure_markVisited(v_fvarId_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0(lean_object* v_00_u03b2_147_, lean_object* v_m_148_, lean_object* v_a_149_, lean_object* v_b_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0___redArg(v_m_148_, v_a_149_, v_b_150_);
return v___x_151_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0(lean_object* v_00_u03b2_152_, lean_object* v_a_153_, lean_object* v_x_154_){
_start:
{
uint8_t v___x_155_; 
v___x_155_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg(v_a_153_, v_x_154_);
return v___x_155_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_153_ = stack[1].m_obj;
lean_object* v_x_154_ = stack[2].m_obj;
uint8_t v_res_156_;
v_res_156_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0(lean_box(0), v_a_153_, v_x_154_);
stack->m_num = v_res_156_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___boxed(lean_object* v_00_u03b2_157_, lean_object* v_a_158_, lean_object* v_x_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0(v_00_u03b2_157_, v_a_158_, v_x_159_);
lean_dec(v_x_159_);
lean_dec(v_a_158_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1(lean_object* v_00_u03b2_162_, lean_object* v_data_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1___redArg(v_data_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_165_, lean_object* v_i_166_, lean_object* v_source_167_, lean_object* v_target_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2___redArg(v_i_166_, v_source_167_, v_target_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_170_, lean_object* v_x_171_, lean_object* v_x_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2_spec__3___redArg(v_x_171_, v_x_172_);
return v___x_173_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0(void){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_instMonadEIO___redArg();
return v___x_174_;
}
}
lean_object* l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5(lean_object* v_msg_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v_toApplicative_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_252_; 
v___x_187_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0);
v___x_188_ = l_StateRefT_x27_instMonad___redArg(v___x_187_);
v_toApplicative_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; 
v_unused_253_ = lean_ctor_get(v___x_188_, 1);
lean_dec(v_unused_253_);
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_252_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_toApplicative_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_252_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v_toFunctor_193_; lean_object* v_toSeq_194_; lean_object* v_toSeqLeft_195_; lean_object* v_toSeqRight_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_250_; 
v_toFunctor_193_ = lean_ctor_get(v_toApplicative_189_, 0);
v_toSeq_194_ = lean_ctor_get(v_toApplicative_189_, 2);
v_toSeqLeft_195_ = lean_ctor_get(v_toApplicative_189_, 3);
v_toSeqRight_196_ = lean_ctor_get(v_toApplicative_189_, 4);
v_isSharedCheck_250_ = !lean_is_exclusive(v_toApplicative_189_);
if (v_isSharedCheck_250_ == 0)
{
lean_object* v_unused_251_; 
v_unused_251_ = lean_ctor_get(v_toApplicative_189_, 1);
lean_dec(v_unused_251_);
v___x_198_ = v_toApplicative_189_;
v_isShared_199_ = v_isSharedCheck_250_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_toSeqRight_196_);
lean_inc(v_toSeqLeft_195_);
lean_inc(v_toSeq_194_);
lean_inc(v_toFunctor_193_);
lean_dec(v_toApplicative_189_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_250_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___f_200_; lean_object* v___f_201_; lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___x_204_; lean_object* v___f_205_; lean_object* v___f_206_; lean_object* v___f_207_; lean_object* v___x_209_; 
v___f_200_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__1));
v___f_201_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__2));
lean_inc_ref(v_toFunctor_193_);
v___f_202_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_202_, 0, v_toFunctor_193_);
v___f_203_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_203_, 0, v_toFunctor_193_);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v___f_202_);
lean_ctor_set(v___x_204_, 1, v___f_203_);
v___f_205_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_205_, 0, v_toSeqRight_196_);
v___f_206_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_206_, 0, v_toSeqLeft_195_);
v___f_207_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_207_, 0, v_toSeq_194_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 4, v___f_205_);
lean_ctor_set(v___x_198_, 3, v___f_206_);
lean_ctor_set(v___x_198_, 2, v___f_207_);
lean_ctor_set(v___x_198_, 1, v___f_200_);
lean_ctor_set(v___x_198_, 0, v___x_204_);
v___x_209_ = v___x_198_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_204_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___f_200_);
lean_ctor_set(v_reuseFailAlloc_249_, 2, v___f_207_);
lean_ctor_set(v_reuseFailAlloc_249_, 3, v___f_206_);
lean_ctor_set(v_reuseFailAlloc_249_, 4, v___f_205_);
v___x_209_ = v_reuseFailAlloc_249_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_211_; 
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v___f_201_);
lean_ctor_set(v___x_191_, 0, v___x_209_);
v___x_211_ = v___x_191_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v___f_201_);
v___x_211_ = v_reuseFailAlloc_248_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_212_; lean_object* v_toApplicative_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_246_; 
v___x_212_ = l_StateRefT_x27_instMonad___redArg(v___x_211_);
v_toApplicative_213_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; 
v_unused_247_ = lean_ctor_get(v___x_212_, 1);
lean_dec(v_unused_247_);
v___x_215_ = v___x_212_;
v_isShared_216_ = v_isSharedCheck_246_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_toApplicative_213_);
lean_dec(v___x_212_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_246_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_toFunctor_217_; lean_object* v_toSeq_218_; lean_object* v_toSeqLeft_219_; lean_object* v_toSeqRight_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_244_; 
v_toFunctor_217_ = lean_ctor_get(v_toApplicative_213_, 0);
v_toSeq_218_ = lean_ctor_get(v_toApplicative_213_, 2);
v_toSeqLeft_219_ = lean_ctor_get(v_toApplicative_213_, 3);
v_toSeqRight_220_ = lean_ctor_get(v_toApplicative_213_, 4);
v_isSharedCheck_244_ = !lean_is_exclusive(v_toApplicative_213_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; 
v_unused_245_ = lean_ctor_get(v_toApplicative_213_, 1);
lean_dec(v_unused_245_);
v___x_222_ = v_toApplicative_213_;
v_isShared_223_ = v_isSharedCheck_244_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_toSeqRight_220_);
lean_inc(v_toSeqLeft_219_);
lean_inc(v_toSeq_218_);
lean_inc(v_toFunctor_217_);
lean_dec(v_toApplicative_213_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_244_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___f_224_; lean_object* v___f_225_; lean_object* v___f_226_; lean_object* v___f_227_; lean_object* v___x_228_; lean_object* v___f_229_; lean_object* v___f_230_; lean_object* v___f_231_; lean_object* v___x_233_; 
v___f_224_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__3));
v___f_225_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__4));
lean_inc_ref(v_toFunctor_217_);
v___f_226_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_226_, 0, v_toFunctor_217_);
v___f_227_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_227_, 0, v_toFunctor_217_);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v___f_226_);
lean_ctor_set(v___x_228_, 1, v___f_227_);
v___f_229_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_229_, 0, v_toSeqRight_220_);
v___f_230_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_230_, 0, v_toSeqLeft_219_);
v___f_231_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_231_, 0, v_toSeq_218_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 4, v___f_229_);
lean_ctor_set(v___x_222_, 3, v___f_230_);
lean_ctor_set(v___x_222_, 2, v___f_231_);
lean_ctor_set(v___x_222_, 1, v___f_224_);
lean_ctor_set(v___x_222_, 0, v___x_228_);
v___x_233_ = v___x_222_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___f_224_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v___f_231_);
lean_ctor_set(v_reuseFailAlloc_243_, 3, v___f_230_);
lean_ctor_set(v_reuseFailAlloc_243_, 4, v___f_229_);
v___x_233_ = v_reuseFailAlloc_243_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_235_; 
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 1, v___f_225_);
lean_ctor_set(v___x_215_, 0, v___x_233_);
v___x_235_ = v___x_215_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v___f_225_);
v___x_235_ = v_reuseFailAlloc_242_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___f_239_; lean_object* v___x_19459__overap_240_; lean_object* v___x_241_; 
v___x_236_ = l_StateRefT_x27_instMonad___redArg(v___x_235_);
v___x_237_ = lean_box(0);
v___x_238_ = l_instInhabitedOfMonad___redArg(v___x_236_, v___x_237_);
v___f_239_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_239_, 0, v___x_238_);
v___x_19459__overap_240_ = lean_panic_fn_borrowed(v___f_239_, v_msg_179_);
lean_dec_ref(v___f_239_);
lean_inc(v___y_185_);
lean_inc_ref(v___y_184_);
lean_inc(v___y_183_);
lean_inc_ref(v___y_182_);
lean_inc(v___y_181_);
lean_inc_ref(v___y_180_);
v___x_241_ = lean_apply_7(v___x_19459__overap_240_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, lean_box(0));
return v___x_241_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_179_ = stack[0].m_obj;
lean_object* v___y_180_ = stack[1].m_obj;
lean_object* v___y_181_ = stack[2].m_obj;
lean_object* v___y_182_ = stack[3].m_obj;
lean_object* v___y_183_ = stack[4].m_obj;
lean_object* v___y_184_ = stack[5].m_obj;
lean_object* v___y_185_ = stack[6].m_obj;
lean_object* v_res_254_;
v_res_254_ = l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5(v_msg_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
stack->m_obj
 = v_res_254_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___boxed(lean_object* v_msg_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5(v_msg_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
return v_res_263_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(lean_object* v_a_264_, lean_object* v_x_265_){
_start:
{
if (lean_obj_tag(v_x_265_) == 0)
{
uint8_t v___x_266_; 
v___x_266_ = 0;
return v___x_266_;
}
else
{
lean_object* v_key_267_; lean_object* v_tail_268_; uint8_t v___x_269_; 
v_key_267_ = lean_ctor_get(v_x_265_, 0);
v_tail_268_ = lean_ctor_get(v_x_265_, 2);
v___x_269_ = lean_expr_eqv(v_key_267_, v_a_264_);
if (v___x_269_ == 0)
{
v_x_265_ = v_tail_268_;
goto _start;
}
else
{
return v___x_269_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_264_ = stack[0].m_obj;
lean_object* v_x_265_ = stack[1].m_obj;
uint8_t v_res_271_;
v_res_271_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(v_a_264_, v_x_265_);
stack->m_num = v_res_271_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg___boxed(lean_object* v_a_272_, lean_object* v_x_273_){
_start:
{
uint8_t v_res_274_; lean_object* v_r_275_; 
v_res_274_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(v_a_272_, v_x_273_);
lean_dec(v_x_273_);
lean_dec_ref(v_a_272_);
v_r_275_ = lean_box(v_res_274_);
return v_r_275_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg(lean_object* v_m_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_buckets_278_; lean_object* v___x_279_; uint64_t v___x_280_; uint64_t v___x_281_; uint64_t v___x_282_; uint64_t v_fold_283_; uint64_t v___x_284_; uint64_t v___x_285_; uint64_t v___x_286_; size_t v___x_287_; size_t v___x_288_; size_t v___x_289_; size_t v___x_290_; size_t v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v_buckets_278_ = lean_ctor_get(v_m_276_, 1);
v___x_279_ = lean_array_get_size(v_buckets_278_);
v___x_280_ = l_Lean_Expr_hash(v_a_277_);
v___x_281_ = 32ULL;
v___x_282_ = lean_uint64_shift_right(v___x_280_, v___x_281_);
v_fold_283_ = lean_uint64_xor(v___x_280_, v___x_282_);
v___x_284_ = 16ULL;
v___x_285_ = lean_uint64_shift_right(v_fold_283_, v___x_284_);
v___x_286_ = lean_uint64_xor(v_fold_283_, v___x_285_);
v___x_287_ = lean_uint64_to_usize(v___x_286_);
v___x_288_ = lean_usize_of_nat(v___x_279_);
v___x_289_ = ((size_t)1ULL);
v___x_290_ = lean_usize_sub(v___x_288_, v___x_289_);
v___x_291_ = lean_usize_land(v___x_287_, v___x_290_);
v___x_292_ = lean_array_uget_borrowed(v_buckets_278_, v___x_291_);
v___x_293_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(v_a_277_, v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_276_ = stack[0].m_obj;
lean_object* v_a_277_ = stack[1].m_obj;
uint8_t v_res_294_;
v_res_294_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg(v_m_276_, v_a_277_);
stack->m_num = v_res_294_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg___boxed(lean_object* v_m_295_, lean_object* v_a_296_){
_start:
{
uint8_t v_res_297_; lean_object* v_r_298_; 
v_res_297_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg(v_m_295_, v_a_296_);
lean_dec_ref(v_a_296_);
lean_dec_ref(v_m_295_);
v_r_298_ = lean_box(v_res_297_);
return v_r_298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18_spec__19___redArg(lean_object* v_x_299_, lean_object* v_x_300_){
_start:
{
if (lean_obj_tag(v_x_300_) == 0)
{
return v_x_299_;
}
else
{
lean_object* v_key_301_; lean_object* v_value_302_; lean_object* v_tail_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_326_; 
v_key_301_ = lean_ctor_get(v_x_300_, 0);
v_value_302_ = lean_ctor_get(v_x_300_, 1);
v_tail_303_ = lean_ctor_get(v_x_300_, 2);
v_isSharedCheck_326_ = !lean_is_exclusive(v_x_300_);
if (v_isSharedCheck_326_ == 0)
{
v___x_305_ = v_x_300_;
v_isShared_306_ = v_isSharedCheck_326_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_tail_303_);
lean_inc(v_value_302_);
lean_inc(v_key_301_);
lean_dec(v_x_300_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_326_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; uint64_t v___x_308_; uint64_t v___x_309_; uint64_t v___x_310_; uint64_t v_fold_311_; uint64_t v___x_312_; uint64_t v___x_313_; uint64_t v___x_314_; size_t v___x_315_; size_t v___x_316_; size_t v___x_317_; size_t v___x_318_; size_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_307_ = lean_array_get_size(v_x_299_);
v___x_308_ = l_Lean_Expr_hash(v_key_301_);
v___x_309_ = 32ULL;
v___x_310_ = lean_uint64_shift_right(v___x_308_, v___x_309_);
v_fold_311_ = lean_uint64_xor(v___x_308_, v___x_310_);
v___x_312_ = 16ULL;
v___x_313_ = lean_uint64_shift_right(v_fold_311_, v___x_312_);
v___x_314_ = lean_uint64_xor(v_fold_311_, v___x_313_);
v___x_315_ = lean_uint64_to_usize(v___x_314_);
v___x_316_ = lean_usize_of_nat(v___x_307_);
v___x_317_ = ((size_t)1ULL);
v___x_318_ = lean_usize_sub(v___x_316_, v___x_317_);
v___x_319_ = lean_usize_land(v___x_315_, v___x_318_);
v___x_320_ = lean_array_uget_borrowed(v_x_299_, v___x_319_);
lean_inc(v___x_320_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 2, v___x_320_);
v___x_322_ = v___x_305_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_key_301_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_value_302_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v___x_320_);
v___x_322_ = v_reuseFailAlloc_325_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; 
v___x_323_ = lean_array_uset(v_x_299_, v___x_319_, v___x_322_);
v_x_299_ = v___x_323_;
v_x_300_ = v_tail_303_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18___redArg(lean_object* v_i_327_, lean_object* v_source_328_, lean_object* v_target_329_){
_start:
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = lean_array_get_size(v_source_328_);
v___x_331_ = lean_nat_dec_lt(v_i_327_, v___x_330_);
if (v___x_331_ == 0)
{
lean_dec_ref(v_source_328_);
lean_dec(v_i_327_);
return v_target_329_;
}
else
{
lean_object* v_es_332_; lean_object* v___x_333_; lean_object* v_source_334_; lean_object* v_target_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_es_332_ = lean_array_fget(v_source_328_, v_i_327_);
v___x_333_ = lean_box(0);
v_source_334_ = lean_array_fset(v_source_328_, v_i_327_, v___x_333_);
v_target_335_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18_spec__19___redArg(v_target_329_, v_es_332_);
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = lean_nat_add(v_i_327_, v___x_336_);
lean_dec(v_i_327_);
v_i_327_ = v___x_337_;
v_source_328_ = v_source_334_;
v_target_329_ = v_target_335_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17___redArg(lean_object* v_data_339_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v_nbuckets_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_340_ = lean_array_get_size(v_data_339_);
v___x_341_ = lean_unsigned_to_nat(2u);
v_nbuckets_342_ = lean_nat_mul(v___x_340_, v___x_341_);
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_box(0);
v___x_345_ = lean_mk_array(v_nbuckets_342_, v___x_344_);
v___x_346_ = lean_array_propagate_mark(v_data_339_, v___x_345_);
v___x_347_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18___redArg(v___x_343_, v_data_339_, v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15___redArg(lean_object* v_m_348_, lean_object* v_a_349_, lean_object* v_b_350_){
_start:
{
lean_object* v_size_351_; lean_object* v_buckets_352_; lean_object* v___x_353_; uint64_t v___x_354_; uint64_t v___x_355_; uint64_t v___x_356_; uint64_t v_fold_357_; uint64_t v___x_358_; uint64_t v___x_359_; uint64_t v___x_360_; size_t v___x_361_; size_t v___x_362_; size_t v___x_363_; size_t v___x_364_; size_t v___x_365_; lean_object* v_bkt_366_; uint8_t v___x_367_; 
v_size_351_ = lean_ctor_get(v_m_348_, 0);
v_buckets_352_ = lean_ctor_get(v_m_348_, 1);
v___x_353_ = lean_array_get_size(v_buckets_352_);
v___x_354_ = l_Lean_Expr_hash(v_a_349_);
v___x_355_ = 32ULL;
v___x_356_ = lean_uint64_shift_right(v___x_354_, v___x_355_);
v_fold_357_ = lean_uint64_xor(v___x_354_, v___x_356_);
v___x_358_ = 16ULL;
v___x_359_ = lean_uint64_shift_right(v_fold_357_, v___x_358_);
v___x_360_ = lean_uint64_xor(v_fold_357_, v___x_359_);
v___x_361_ = lean_uint64_to_usize(v___x_360_);
v___x_362_ = lean_usize_of_nat(v___x_353_);
v___x_363_ = ((size_t)1ULL);
v___x_364_ = lean_usize_sub(v___x_362_, v___x_363_);
v___x_365_ = lean_usize_land(v___x_361_, v___x_364_);
v_bkt_366_ = lean_array_uget_borrowed(v_buckets_352_, v___x_365_);
v___x_367_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(v_a_349_, v_bkt_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_388_; 
lean_inc_ref(v_buckets_352_);
lean_inc(v_size_351_);
v_isSharedCheck_388_ = !lean_is_exclusive(v_m_348_);
if (v_isSharedCheck_388_ == 0)
{
lean_object* v_unused_389_; lean_object* v_unused_390_; 
v_unused_389_ = lean_ctor_get(v_m_348_, 1);
lean_dec(v_unused_389_);
v_unused_390_ = lean_ctor_get(v_m_348_, 0);
lean_dec(v_unused_390_);
v___x_369_ = v_m_348_;
v_isShared_370_ = v_isSharedCheck_388_;
goto v_resetjp_368_;
}
else
{
lean_dec(v_m_348_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_388_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v_size_x27_372_; lean_object* v___x_373_; lean_object* v_buckets_x27_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_371_ = lean_unsigned_to_nat(1u);
v_size_x27_372_ = lean_nat_add(v_size_351_, v___x_371_);
lean_dec(v_size_351_);
lean_inc(v_bkt_366_);
v___x_373_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_373_, 0, v_a_349_);
lean_ctor_set(v___x_373_, 1, v_b_350_);
lean_ctor_set(v___x_373_, 2, v_bkt_366_);
v_buckets_x27_374_ = lean_array_uset(v_buckets_352_, v___x_365_, v___x_373_);
v___x_375_ = lean_unsigned_to_nat(4u);
v___x_376_ = lean_nat_mul(v_size_x27_372_, v___x_375_);
v___x_377_ = lean_unsigned_to_nat(3u);
v___x_378_ = lean_nat_div(v___x_376_, v___x_377_);
lean_dec(v___x_376_);
v___x_379_ = lean_array_get_size(v_buckets_x27_374_);
v___x_380_ = lean_nat_dec_le(v___x_378_, v___x_379_);
lean_dec(v___x_378_);
if (v___x_380_ == 0)
{
lean_object* v_val_381_; lean_object* v___x_383_; 
v_val_381_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17___redArg(v_buckets_x27_374_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v_val_381_);
lean_ctor_set(v___x_369_, 0, v_size_x27_372_);
v___x_383_ = v___x_369_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_size_x27_372_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_val_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
else
{
lean_object* v___x_386_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v_buckets_x27_374_);
lean_ctor_set(v___x_369_, 0, v_size_x27_372_);
v___x_386_ = v___x_369_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_size_x27_372_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_buckets_x27_374_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
else
{
lean_dec(v_b_350_);
lean_dec_ref(v_a_349_);
return v_m_348_;
}
}
}
lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg(lean_object* v_e_391_, lean_object* v_a_392_){
_start:
{
lean_object* v___x_394_; lean_object* v_checked_395_; uint8_t v___x_396_; 
v___x_394_ = lean_st_ref_get(v_a_392_);
v_checked_395_ = lean_ctor_get(v___x_394_, 1);
lean_inc_ref(v_checked_395_);
lean_dec(v___x_394_);
v___x_396_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg(v_checked_395_, v_e_391_);
lean_dec_ref(v_checked_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v_visited_398_; lean_object* v_checked_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_411_; 
v___x_397_ = lean_st_ref_take(v_a_392_);
v_visited_398_ = lean_ctor_get(v___x_397_, 0);
v_checked_399_ = lean_ctor_get(v___x_397_, 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_411_ == 0)
{
v___x_401_ = v___x_397_;
v_isShared_402_ = v_isSharedCheck_411_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_checked_399_);
lean_inc(v_visited_398_);
lean_dec(v___x_397_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_411_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_403_ = lean_box(0);
v___x_404_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15___redArg(v_checked_399_, v_e_391_, v___x_403_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 1, v___x_404_);
v___x_406_ = v___x_401_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_visited_398_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_404_);
v___x_406_ = v_reuseFailAlloc_410_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_407_ = lean_st_ref_put(v_a_392_, v___x_406_);
v___x_408_ = lean_box(v___x_396_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
}
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; 
lean_dec_ref(v_e_391_);
v___x_412_ = lean_box(v___x_396_);
v___x_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
return v___x_413_;
}
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_391_ = stack[0].m_obj;
lean_object* v_a_392_ = stack[1].m_obj;
lean_object* v_res_414_;
v_res_414_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg(v_e_391_, v_a_392_);
stack->m_obj
 = v_res_414_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg___boxed(lean_object* v_e_415_, lean_object* v_a_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg(v_e_415_, v_a_416_);
lean_dec(v_a_416_);
return v_res_418_;
}
}
lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg(lean_object* v_e_419_, lean_object* v_a_420_){
_start:
{
lean_object* v___x_422_; lean_object* v_visited_423_; size_t v___x_424_; size_t v___x_425_; size_t v___x_426_; lean_object* v___x_427_; size_t v___x_428_; uint8_t v___x_429_; 
v___x_422_ = lean_st_ref_get(v_a_420_);
v_visited_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc_ref(v_visited_423_);
lean_dec(v___x_422_);
v___x_424_ = lean_ptr_addr(v_e_419_);
v___x_425_ = ((size_t)8191ULL);
v___x_426_ = lean_usize_mod(v___x_424_, v___x_425_);
v___x_427_ = lean_array_uget(v_visited_423_, v___x_426_);
lean_dec_ref(v_visited_423_);
v___x_428_ = lean_ptr_addr(v___x_427_);
lean_dec(v___x_427_);
v___x_429_ = lean_usize_dec_eq(v___x_428_, v___x_424_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v_visited_431_; lean_object* v_checked_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_443_; 
v___x_430_ = lean_st_ref_take(v_a_420_);
v_visited_431_ = lean_ctor_get(v___x_430_, 0);
v_checked_432_ = lean_ctor_get(v___x_430_, 1);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_443_ == 0)
{
v___x_434_ = v___x_430_;
v_isShared_435_ = v_isSharedCheck_443_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_checked_432_);
lean_inc(v_visited_431_);
lean_dec(v___x_430_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_443_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = lean_array_uset(v_visited_431_, v___x_426_, v_e_419_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_436_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_checked_432_);
v___x_438_ = v_reuseFailAlloc_442_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lean_st_ref_put(v_a_420_, v___x_438_);
v___x_440_ = lean_box(v___x_429_);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
}
else
{
lean_object* v___x_444_; lean_object* v___x_445_; 
lean_dec_ref(v_e_419_);
v___x_444_ = lean_box(v___x_429_);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_419_ = stack[0].m_obj;
lean_object* v_a_420_ = stack[1].m_obj;
lean_object* v_res_446_;
v_res_446_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg(v_e_419_, v_a_420_);
stack->m_obj
 = v_res_446_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg___boxed(lean_object* v_e_447_, lean_object* v_a_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg(v_e_447_, v_a_448_);
lean_dec(v_a_448_);
return v_res_450_;
}
}
lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(lean_object* v_p_451_, lean_object* v_f_452_, uint8_t v_stopWhenVisited_453_, lean_object* v_e_454_, lean_object* v_a_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v_d_470_; lean_object* v_b_471_; lean_object* v___y_472_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___x_503_; 
lean_inc_ref(v_e_454_);
v___x_503_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg(v_e_454_, v_a_455_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_536_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_536_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_536_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_536_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
uint8_t v___x_508_; 
v___x_508_ = lean_unbox(v_a_504_);
lean_dec(v_a_504_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; uint8_t v___x_510_; 
lean_del_object(v___x_506_);
lean_inc_ref(v_p_451_);
lean_inc_ref(v_e_454_);
v___x_509_ = lean_apply_1(v_p_451_, v_e_454_);
v___x_510_ = lean_unbox(v___x_509_);
if (v___x_510_ == 0)
{
v___y_476_ = v_a_455_;
v___y_477_ = v___y_456_;
v___y_478_ = v___y_457_;
v___y_479_ = v___y_458_;
v___y_480_ = v___y_459_;
v___y_481_ = v___y_460_;
v___y_482_ = v___y_461_;
goto v___jp_475_;
}
else
{
lean_object* v___x_511_; 
lean_inc_ref(v_e_454_);
v___x_511_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg(v_e_454_, v_a_455_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; uint8_t v___x_513_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
v___x_513_ = lean_unbox(v_a_512_);
lean_dec(v_a_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
lean_inc_ref(v_f_452_);
lean_inc(v___y_461_);
lean_inc_ref(v___y_460_);
lean_inc(v___y_459_);
lean_inc_ref(v___y_458_);
lean_inc(v___y_457_);
lean_inc_ref(v___y_456_);
lean_inc_ref(v_e_454_);
v___x_514_ = lean_apply_8(v_f_452_, v_e_454_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, lean_box(0));
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_522_; 
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_522_ == 0)
{
lean_object* v_unused_523_; 
v_unused_523_ = lean_ctor_get(v___x_514_, 0);
lean_dec(v_unused_523_);
v___x_516_ = v___x_514_;
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
else
{
lean_dec(v___x_514_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
if (v_stopWhenVisited_453_ == 0)
{
lean_del_object(v___x_516_);
v___y_476_ = v_a_455_;
v___y_477_ = v___y_456_;
v___y_478_ = v___y_457_;
v___y_479_ = v___y_458_;
v___y_480_ = v___y_459_;
v___y_481_ = v___y_460_;
v___y_482_ = v___y_461_;
goto v___jp_475_;
}
else
{
lean_object* v___x_518_; lean_object* v___x_520_; 
lean_dec_ref(v_e_454_);
lean_dec_ref(v_f_452_);
lean_dec_ref(v_p_451_);
v___x_518_ = lean_box(0);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_518_);
v___x_520_ = v___x_516_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
else
{
lean_dec_ref(v_e_454_);
lean_dec_ref(v_f_452_);
lean_dec_ref(v_p_451_);
return v___x_514_;
}
}
else
{
v___y_476_ = v_a_455_;
v___y_477_ = v___y_456_;
v___y_478_ = v___y_457_;
v___y_479_ = v___y_458_;
v___y_480_ = v___y_459_;
v___y_481_ = v___y_460_;
v___y_482_ = v___y_461_;
goto v___jp_475_;
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_dec_ref(v_e_454_);
lean_dec_ref(v_f_452_);
lean_dec_ref(v_p_451_);
v_a_524_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_511_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_511_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
else
{
lean_object* v___x_532_; lean_object* v___x_534_; 
lean_dec_ref(v_e_454_);
lean_dec_ref(v_f_452_);
lean_dec_ref(v_p_451_);
v___x_532_ = lean_box(0);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_532_);
v___x_534_ = v___x_506_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec_ref(v_e_454_);
lean_dec_ref(v_f_452_);
lean_dec_ref(v_p_451_);
v_a_537_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_503_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_503_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
v___jp_463_:
{
lean_object* v___x_473_; 
lean_inc_ref(v_f_452_);
lean_inc_ref(v_p_451_);
v___x_473_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_451_, v_f_452_, v_stopWhenVisited_453_, v_d_470_, v___y_472_, v___y_466_, v___y_464_, v___y_469_, v___y_468_, v___y_465_, v___y_467_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_dec_ref_known(v___x_473_, 1);
v_e_454_ = v_b_471_;
v_a_455_ = v___y_472_;
v___y_456_ = v___y_466_;
v___y_457_ = v___y_464_;
v___y_458_ = v___y_469_;
v___y_459_ = v___y_468_;
v___y_460_ = v___y_465_;
v___y_461_ = v___y_467_;
goto _start;
}
else
{
lean_dec_ref(v_b_471_);
lean_dec_ref(v_f_452_);
lean_dec_ref(v_p_451_);
return v___x_473_;
}
}
v___jp_475_:
{
switch(lean_obj_tag(v_e_454_))
{
case 7:
{
lean_object* v_binderType_483_; lean_object* v_body_484_; 
v_binderType_483_ = lean_ctor_get(v_e_454_, 1);
lean_inc_ref(v_binderType_483_);
v_body_484_ = lean_ctor_get(v_e_454_, 2);
lean_inc_ref(v_body_484_);
lean_dec_ref_known(v_e_454_, 3);
v___y_464_ = v___y_478_;
v___y_465_ = v___y_481_;
v___y_466_ = v___y_477_;
v___y_467_ = v___y_482_;
v___y_468_ = v___y_480_;
v___y_469_ = v___y_479_;
v_d_470_ = v_binderType_483_;
v_b_471_ = v_body_484_;
v___y_472_ = v___y_476_;
goto v___jp_463_;
}
case 6:
{
lean_object* v_binderType_485_; lean_object* v_body_486_; 
v_binderType_485_ = lean_ctor_get(v_e_454_, 1);
lean_inc_ref(v_binderType_485_);
v_body_486_ = lean_ctor_get(v_e_454_, 2);
lean_inc_ref(v_body_486_);
lean_dec_ref_known(v_e_454_, 3);
v___y_464_ = v___y_478_;
v___y_465_ = v___y_481_;
v___y_466_ = v___y_477_;
v___y_467_ = v___y_482_;
v___y_468_ = v___y_480_;
v___y_469_ = v___y_479_;
v_d_470_ = v_binderType_485_;
v_b_471_ = v_body_486_;
v___y_472_ = v___y_476_;
goto v___jp_463_;
}
case 8:
{
lean_object* v_type_487_; lean_object* v_value_488_; lean_object* v_body_489_; lean_object* v___x_490_; 
v_type_487_ = lean_ctor_get(v_e_454_, 1);
lean_inc_ref(v_type_487_);
v_value_488_ = lean_ctor_get(v_e_454_, 2);
lean_inc_ref(v_value_488_);
v_body_489_ = lean_ctor_get(v_e_454_, 3);
lean_inc_ref(v_body_489_);
lean_dec_ref_known(v_e_454_, 4);
lean_inc_ref(v_f_452_);
lean_inc_ref(v_p_451_);
v___x_490_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_451_, v_f_452_, v_stopWhenVisited_453_, v_type_487_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v___x_491_; 
lean_dec_ref_known(v___x_490_, 1);
lean_inc_ref(v_f_452_);
lean_inc_ref(v_p_451_);
v___x_491_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_451_, v_f_452_, v_stopWhenVisited_453_, v_value_488_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_dec_ref_known(v___x_491_, 1);
v_e_454_ = v_body_489_;
v_a_455_ = v___y_476_;
v___y_456_ = v___y_477_;
v___y_457_ = v___y_478_;
v___y_458_ = v___y_479_;
v___y_459_ = v___y_480_;
v___y_460_ = v___y_481_;
v___y_461_ = v___y_482_;
goto _start;
}
else
{
lean_dec_ref(v_body_489_);
lean_dec_ref(v_f_452_);
lean_dec_ref(v_p_451_);
return v___x_491_;
}
}
else
{
lean_dec_ref(v_body_489_);
lean_dec_ref(v_value_488_);
lean_dec_ref(v_f_452_);
lean_dec_ref(v_p_451_);
return v___x_490_;
}
}
case 5:
{
lean_object* v_fn_493_; lean_object* v_arg_494_; lean_object* v___x_495_; 
v_fn_493_ = lean_ctor_get(v_e_454_, 0);
lean_inc_ref(v_fn_493_);
v_arg_494_ = lean_ctor_get(v_e_454_, 1);
lean_inc_ref(v_arg_494_);
lean_dec_ref_known(v_e_454_, 2);
lean_inc_ref(v_f_452_);
lean_inc_ref(v_p_451_);
v___x_495_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_451_, v_f_452_, v_stopWhenVisited_453_, v_fn_493_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_dec_ref_known(v___x_495_, 1);
v_e_454_ = v_arg_494_;
v_a_455_ = v___y_476_;
v___y_456_ = v___y_477_;
v___y_457_ = v___y_478_;
v___y_458_ = v___y_479_;
v___y_459_ = v___y_480_;
v___y_460_ = v___y_481_;
v___y_461_ = v___y_482_;
goto _start;
}
else
{
lean_dec_ref(v_arg_494_);
lean_dec_ref(v_f_452_);
lean_dec_ref(v_p_451_);
return v___x_495_;
}
}
case 10:
{
lean_object* v_expr_497_; 
v_expr_497_ = lean_ctor_get(v_e_454_, 1);
lean_inc_ref(v_expr_497_);
lean_dec_ref_known(v_e_454_, 2);
v_e_454_ = v_expr_497_;
v_a_455_ = v___y_476_;
v___y_456_ = v___y_477_;
v___y_457_ = v___y_478_;
v___y_458_ = v___y_479_;
v___y_459_ = v___y_480_;
v___y_460_ = v___y_481_;
v___y_461_ = v___y_482_;
goto _start;
}
case 11:
{
lean_object* v_struct_499_; 
v_struct_499_ = lean_ctor_get(v_e_454_, 2);
lean_inc_ref(v_struct_499_);
lean_dec_ref_known(v_e_454_, 3);
v_e_454_ = v_struct_499_;
v_a_455_ = v___y_476_;
v___y_456_ = v___y_477_;
v___y_457_ = v___y_478_;
v___y_458_ = v___y_479_;
v___y_459_ = v___y_480_;
v___y_460_ = v___y_481_;
v___y_461_ = v___y_482_;
goto _start;
}
default: 
{
lean_object* v___x_501_; lean_object* v___x_502_; 
lean_dec_ref(v_e_454_);
lean_dec_ref(v_f_452_);
lean_dec_ref(v_p_451_);
v___x_501_ = lean_box(0);
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_451_ = stack[0].m_obj;
lean_object* v_f_452_ = stack[1].m_obj;
uint8_t v_stopWhenVisited_453_ = stack[2].m_num;
lean_object* v_e_454_ = stack[3].m_obj;
lean_object* v_a_455_ = stack[4].m_obj;
lean_object* v___y_456_ = stack[5].m_obj;
lean_object* v___y_457_ = stack[6].m_obj;
lean_object* v___y_458_ = stack[7].m_obj;
lean_object* v___y_459_ = stack[8].m_obj;
lean_object* v___y_460_ = stack[9].m_obj;
lean_object* v___y_461_ = stack[10].m_obj;
lean_object* v_res_545_;
v_res_545_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_451_, v_f_452_, v_stopWhenVisited_453_, v_e_454_, v_a_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
stack->m_obj
 = v_res_545_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4___boxed(lean_object* v_p_546_, lean_object* v_f_547_, lean_object* v_stopWhenVisited_548_, lean_object* v_e_549_, lean_object* v_a_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
uint8_t v_stopWhenVisited_boxed_558_; lean_object* v_res_559_; 
v_stopWhenVisited_boxed_558_ = lean_unbox(v_stopWhenVisited_548_);
v_res_559_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_546_, v_f_547_, v_stopWhenVisited_boxed_558_, v_e_549_, v_a_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v_a_550_);
return v_res_559_;
}
}
lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2(lean_object* v_p_560_, lean_object* v_f_561_, lean_object* v_e_562_, uint8_t v_stopWhenVisited_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = l_Lean_ForEachExprWhere_initCache;
v___x_572_ = lean_st_mk_ref(v___x_571_);
v___x_573_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_560_, v_f_561_, v_stopWhenVisited_563_, v_e_562_, v___x_572_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_582_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_582_ == 0)
{
v___x_576_ = v___x_573_;
v_isShared_577_ = v_isSharedCheck_582_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_573_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_582_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_578_ = lean_st_ref_get(v___x_572_);
lean_dec(v___x_572_);
lean_dec(v___x_578_);
if (v_isShared_577_ == 0)
{
v___x_580_ = v___x_576_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_574_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
else
{
lean_dec(v___x_572_);
return v___x_573_;
}
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_560_ = stack[0].m_obj;
lean_object* v_f_561_ = stack[1].m_obj;
lean_object* v_e_562_ = stack[2].m_obj;
uint8_t v_stopWhenVisited_563_ = stack[3].m_num;
lean_object* v___y_564_ = stack[4].m_obj;
lean_object* v___y_565_ = stack[5].m_obj;
lean_object* v___y_566_ = stack[6].m_obj;
lean_object* v___y_567_ = stack[7].m_obj;
lean_object* v___y_568_ = stack[8].m_obj;
lean_object* v___y_569_ = stack[9].m_obj;
lean_object* v_res_583_;
v_res_583_ = l_Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2(v_p_560_, v_f_561_, v_e_562_, v_stopWhenVisited_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
stack->m_obj
 = v_res_583_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2___boxed(lean_object* v_p_584_, lean_object* v_f_585_, lean_object* v_e_586_, lean_object* v_stopWhenVisited_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
uint8_t v_stopWhenVisited_boxed_595_; lean_object* v_res_596_; 
v_stopWhenVisited_boxed_595_ = lean_unbox(v_stopWhenVisited_587_);
v_res_596_ = l_Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2(v_p_584_, v_f_585_, v_e_586_, v_stopWhenVisited_boxed_595_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
return v_res_596_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg(lean_object* v_m_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_buckets_599_; lean_object* v___x_600_; uint64_t v___x_601_; uint64_t v___x_602_; uint64_t v___x_603_; uint64_t v_fold_604_; uint64_t v___x_605_; uint64_t v___x_606_; uint64_t v___x_607_; size_t v___x_608_; size_t v___x_609_; size_t v___x_610_; size_t v___x_611_; size_t v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_buckets_599_ = lean_ctor_get(v_m_597_, 1);
v___x_600_ = lean_array_get_size(v_buckets_599_);
v___x_601_ = l_Lean_instHashableFVarId_hash(v_a_598_);
v___x_602_ = 32ULL;
v___x_603_ = lean_uint64_shift_right(v___x_601_, v___x_602_);
v_fold_604_ = lean_uint64_xor(v___x_601_, v___x_603_);
v___x_605_ = 16ULL;
v___x_606_ = lean_uint64_shift_right(v_fold_604_, v___x_605_);
v___x_607_ = lean_uint64_xor(v_fold_604_, v___x_606_);
v___x_608_ = lean_uint64_to_usize(v___x_607_);
v___x_609_ = lean_usize_of_nat(v___x_600_);
v___x_610_ = ((size_t)1ULL);
v___x_611_ = lean_usize_sub(v___x_609_, v___x_610_);
v___x_612_ = lean_usize_land(v___x_608_, v___x_611_);
v___x_613_ = lean_array_uget_borrowed(v_buckets_599_, v___x_612_);
v___x_614_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg(v_a_598_, v___x_613_);
return v___x_614_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_597_ = stack[0].m_obj;
lean_object* v_a_598_ = stack[1].m_obj;
uint8_t v_res_615_;
v_res_615_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg(v_m_597_, v_a_598_);
stack->m_num = v_res_615_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg___boxed(lean_object* v_m_616_, lean_object* v_a_617_){
_start:
{
uint8_t v_res_618_; lean_object* v_r_619_; 
v_res_618_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg(v_m_616_, v_a_617_);
lean_dec(v_a_617_);
lean_dec_ref(v_m_616_);
v_r_619_ = lean_box(v_res_618_);
return v_r_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType___lam__0___boxed(lean_object* v_e_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Compiler_LCNF_Closure_collectType___lam__0(v_e_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec_ref(v_e_620_);
return v_res_628_;
}
}
lean_object* l_Lean_Compiler_LCNF_Closure_collectType(lean_object* v_type_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
uint8_t v___x_638_; 
v___x_638_ = l_Lean_Expr_hasFVar(v_type_630_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; 
lean_dec_ref(v_type_630_);
v___x_639_ = lean_box(0);
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
return v___x_640_;
}
else
{
lean_object* v___f_641_; lean_object* v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; 
v___f_641_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lam__0___boxed), 8, 0);
v___x_642_ = ((lean_object*)(l_Lean_Compiler_LCNF_Closure_collectType___closed__0));
v___x_643_ = 0;
v___x_644_ = l_Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2(v___x_642_, v___f_641_, v_type_630_, v___x_643_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_644_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Closure_collectType_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_630_ = stack[0].m_obj;
lean_object* v_a_631_ = stack[1].m_obj;
lean_object* v_a_632_ = stack[2].m_obj;
lean_object* v_a_633_ = stack[3].m_obj;
lean_object* v_a_634_ = stack[4].m_obj;
lean_object* v_a_635_ = stack[5].m_obj;
lean_object* v_a_636_ = stack[6].m_obj;
lean_object* v_res_645_;
v_res_645_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
stack->m_obj
 = v_res_645_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0(lean_object* v_as_646_, size_t v_i_647_, size_t v_stop_648_, lean_object* v_b_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
uint8_t v___x_657_; 
v___x_657_ = lean_usize_dec_eq(v_i_647_, v_stop_648_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v_type_659_; lean_object* v___x_660_; 
v___x_658_ = lean_array_uget_borrowed(v_as_646_, v_i_647_);
v_type_659_ = lean_ctor_get(v___x_658_, 2);
lean_inc_ref(v_type_659_);
v___x_660_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_659_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; size_t v___x_662_; size_t v___x_663_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref_known(v___x_660_, 1);
v___x_662_ = ((size_t)1ULL);
v___x_663_ = lean_usize_add(v_i_647_, v___x_662_);
v_i_647_ = v___x_663_;
v_b_649_ = v_a_661_;
goto _start;
}
else
{
return v___x_660_;
}
}
else
{
lean_object* v___x_665_; 
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v_b_649_);
return v___x_665_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_646_ = stack[0].m_obj;
size_t v_i_647_ = stack[1].m_num;
size_t v_stop_648_ = stack[2].m_num;
lean_object* v_b_649_ = stack[3].m_obj;
lean_object* v___y_650_ = stack[4].m_obj;
lean_object* v___y_651_ = stack[5].m_obj;
lean_object* v___y_652_ = stack[6].m_obj;
lean_object* v___y_653_ = stack[7].m_obj;
lean_object* v___y_654_ = stack[8].m_obj;
lean_object* v___y_655_ = stack[9].m_obj;
lean_object* v_res_666_;
v_res_666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0(v_as_646_, v_i_647_, v_stop_648_, v_b_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
stack->m_obj
 = v_res_666_;
}
lean_object* l_Lean_Compiler_LCNF_Closure_collectParams(lean_object* v_params_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = lean_array_get_size(v_params_667_);
v___x_677_ = lean_box(0);
v___x_678_ = lean_nat_dec_lt(v___x_675_, v___x_676_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_677_);
return v___x_679_;
}
else
{
uint8_t v___x_680_; 
v___x_680_ = lean_nat_dec_le(v___x_676_, v___x_676_);
if (v___x_680_ == 0)
{
if (v___x_678_ == 0)
{
lean_object* v___x_681_; 
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_677_);
return v___x_681_;
}
else
{
size_t v___x_682_; size_t v___x_683_; lean_object* v___x_684_; 
v___x_682_ = ((size_t)0ULL);
v___x_683_ = lean_usize_of_nat(v___x_676_);
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0(v_params_667_, v___x_682_, v___x_683_, v___x_677_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
return v___x_684_;
}
}
else
{
size_t v___x_685_; size_t v___x_686_; lean_object* v___x_687_; 
v___x_685_ = ((size_t)0ULL);
v___x_686_ = lean_usize_of_nat(v___x_676_);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0(v_params_667_, v___x_685_, v___x_686_, v___x_677_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
return v___x_687_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Closure_collectParams_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_667_ = stack[0].m_obj;
lean_object* v_a_668_ = stack[1].m_obj;
lean_object* v_a_669_ = stack[2].m_obj;
lean_object* v_a_670_ = stack[3].m_obj;
lean_object* v_a_671_ = stack[4].m_obj;
lean_object* v_a_672_ = stack[5].m_obj;
lean_object* v_a_673_ = stack[6].m_obj;
lean_object* v_res_688_;
v_res_688_ = l_Lean_Compiler_LCNF_Closure_collectParams(v_params_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
stack->m_obj
 = v_res_688_;
}
lean_object* l_Lean_Compiler_LCNF_Closure_collectArg(lean_object* v_arg_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
switch(lean_obj_tag(v_arg_689_))
{
case 0:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_box(0);
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
case 1:
{
lean_object* v_fvarId_699_; lean_object* v___x_700_; 
v_fvarId_699_ = lean_ctor_get(v_arg_689_, 0);
lean_inc(v_fvarId_699_);
lean_dec_ref_known(v_arg_689_, 1);
v___x_700_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v_fvarId_699_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
return v___x_700_;
}
default: 
{
lean_object* v_expr_701_; lean_object* v___x_702_; 
v_expr_701_ = lean_ctor_get(v_arg_689_, 0);
lean_inc_ref(v_expr_701_);
lean_dec_ref_known(v_arg_689_, 1);
v___x_702_ = l_Lean_Compiler_LCNF_Closure_collectType(v_expr_701_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
return v___x_702_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Closure_collectArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_689_ = stack[0].m_obj;
lean_object* v_a_690_ = stack[1].m_obj;
lean_object* v_a_691_ = stack[2].m_obj;
lean_object* v_a_692_ = stack[3].m_obj;
lean_object* v_a_693_ = stack[4].m_obj;
lean_object* v_a_694_ = stack[5].m_obj;
lean_object* v_a_695_ = stack[6].m_obj;
lean_object* v_res_703_;
v_res_703_ = l_Lean_Compiler_LCNF_Closure_collectArg(v_arg_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
stack->m_obj
 = v_res_703_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(lean_object* v_as_704_, size_t v_i_705_, size_t v_stop_706_, lean_object* v_b_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
uint8_t v___x_715_; 
v___x_715_ = lean_usize_dec_eq(v_i_705_, v_stop_706_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_array_uget_borrowed(v_as_704_, v_i_705_);
lean_inc(v___x_716_);
v___x_717_ = l_Lean_Compiler_LCNF_Closure_collectArg(v___x_716_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; size_t v___x_719_; size_t v___x_720_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 1);
v___x_719_ = ((size_t)1ULL);
v___x_720_ = lean_usize_add(v_i_705_, v___x_719_);
v_i_705_ = v___x_720_;
v_b_707_ = v_a_718_;
goto _start;
}
else
{
return v___x_717_;
}
}
else
{
lean_object* v___x_722_; 
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v_b_707_);
return v___x_722_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_704_ = stack[0].m_obj;
size_t v_i_705_ = stack[1].m_num;
size_t v_stop_706_ = stack[2].m_num;
lean_object* v_b_707_ = stack[3].m_obj;
lean_object* v___y_708_ = stack[4].m_obj;
lean_object* v___y_709_ = stack[5].m_obj;
lean_object* v___y_710_ = stack[6].m_obj;
lean_object* v___y_711_ = stack[7].m_obj;
lean_object* v___y_712_ = stack[8].m_obj;
lean_object* v___y_713_ = stack[9].m_obj;
lean_object* v_res_723_;
v_res_723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_as_704_, v_i_705_, v_stop_706_, v_b_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
stack->m_obj
 = v_res_723_;
}
lean_object* l_Lean_Compiler_LCNF_Closure_collectLetValue(lean_object* v_e_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
switch(lean_obj_tag(v_e_724_))
{
case 2:
{
lean_object* v_struct_732_; lean_object* v___x_733_; 
v_struct_732_ = lean_ctor_get(v_e_724_, 2);
lean_inc(v_struct_732_);
lean_dec_ref_known(v_e_724_, 3);
v___x_733_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v_struct_732_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
return v___x_733_;
}
case 3:
{
lean_object* v_args_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v_args_734_ = lean_ctor_get(v_e_724_, 2);
lean_inc_ref(v_args_734_);
lean_dec_ref_known(v_e_724_, 3);
v___x_735_ = lean_unsigned_to_nat(0u);
v___x_736_ = lean_array_get_size(v_args_734_);
v___x_737_ = lean_box(0);
v___x_738_ = lean_nat_dec_lt(v___x_735_, v___x_736_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; 
lean_dec_ref(v_args_734_);
v___x_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
return v___x_739_;
}
else
{
uint8_t v___x_740_; 
v___x_740_ = lean_nat_dec_le(v___x_736_, v___x_736_);
if (v___x_740_ == 0)
{
if (v___x_738_ == 0)
{
lean_object* v___x_741_; 
lean_dec_ref(v_args_734_);
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_737_);
return v___x_741_;
}
else
{
size_t v___x_742_; size_t v___x_743_; lean_object* v___x_744_; 
v___x_742_ = ((size_t)0ULL);
v___x_743_ = lean_usize_of_nat(v___x_736_);
v___x_744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_734_, v___x_742_, v___x_743_, v___x_737_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
lean_dec_ref(v_args_734_);
return v___x_744_;
}
}
else
{
size_t v___x_745_; size_t v___x_746_; lean_object* v___x_747_; 
v___x_745_ = ((size_t)0ULL);
v___x_746_ = lean_usize_of_nat(v___x_736_);
v___x_747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_734_, v___x_745_, v___x_746_, v___x_737_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
lean_dec_ref(v_args_734_);
return v___x_747_;
}
}
}
case 4:
{
lean_object* v_fvarId_748_; lean_object* v_args_749_; lean_object* v___x_750_; 
v_fvarId_748_ = lean_ctor_get(v_e_724_, 0);
lean_inc(v_fvarId_748_);
v_args_749_ = lean_ctor_get(v_e_724_, 1);
lean_inc_ref(v_args_749_);
lean_dec_ref_known(v_e_724_, 2);
v___x_750_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v_fvarId_748_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_771_; 
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; 
v_unused_772_ = lean_ctor_get(v___x_750_, 0);
lean_dec(v_unused_772_);
v___x_752_ = v___x_750_;
v_isShared_753_ = v_isSharedCheck_771_;
goto v_resetjp_751_;
}
else
{
lean_dec(v___x_750_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_771_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_754_ = lean_unsigned_to_nat(0u);
v___x_755_ = lean_array_get_size(v_args_749_);
v___x_756_ = lean_box(0);
v___x_757_ = lean_nat_dec_lt(v___x_754_, v___x_755_);
if (v___x_757_ == 0)
{
lean_object* v___x_759_; 
lean_dec_ref(v_args_749_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_756_);
v___x_759_ = v___x_752_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_756_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
else
{
uint8_t v___x_761_; 
v___x_761_ = lean_nat_dec_le(v___x_755_, v___x_755_);
if (v___x_761_ == 0)
{
if (v___x_757_ == 0)
{
lean_object* v___x_763_; 
lean_dec_ref(v_args_749_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_756_);
v___x_763_ = v___x_752_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_756_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
else
{
size_t v___x_765_; size_t v___x_766_; lean_object* v___x_767_; 
lean_del_object(v___x_752_);
v___x_765_ = ((size_t)0ULL);
v___x_766_ = lean_usize_of_nat(v___x_755_);
v___x_767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_749_, v___x_765_, v___x_766_, v___x_756_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
lean_dec_ref(v_args_749_);
return v___x_767_;
}
}
else
{
size_t v___x_768_; size_t v___x_769_; lean_object* v___x_770_; 
lean_del_object(v___x_752_);
v___x_768_ = ((size_t)0ULL);
v___x_769_ = lean_usize_of_nat(v___x_755_);
v___x_770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_749_, v___x_768_, v___x_769_, v___x_756_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
lean_dec_ref(v_args_749_);
return v___x_770_;
}
}
}
}
else
{
lean_dec_ref(v_args_749_);
return v___x_750_;
}
}
default: 
{
lean_object* v___x_773_; lean_object* v___x_774_; 
lean_dec(v_e_724_);
v___x_773_ = lean_box(0);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Closure_collectLetValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_724_ = stack[0].m_obj;
lean_object* v_a_725_ = stack[1].m_obj;
lean_object* v_a_726_ = stack[2].m_obj;
lean_object* v_a_727_ = stack[3].m_obj;
lean_object* v_a_728_ = stack[4].m_obj;
lean_object* v_a_729_ = stack[5].m_obj;
lean_object* v_a_730_ = stack[6].m_obj;
lean_object* v_res_775_;
v_res_775_ = l_Lean_Compiler_LCNF_Closure_collectLetValue(v_e_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
stack->m_obj
 = v_res_775_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11(lean_object* v_as_776_, size_t v_i_777_, size_t v_stop_778_, lean_object* v_b_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___y_788_; uint8_t v___x_793_; 
v___x_793_ = lean_usize_dec_eq(v_i_777_, v_stop_778_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; 
v___x_794_ = lean_array_uget_borrowed(v_as_776_, v_i_777_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_params_795_; lean_object* v_code_796_; lean_object* v___x_797_; 
v_params_795_ = lean_ctor_get(v___x_794_, 1);
v_code_796_ = lean_ctor_get(v___x_794_, 2);
v___x_797_ = l_Lean_Compiler_LCNF_Closure_collectParams(v_params_795_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v___x_798_; 
lean_dec_ref_known(v___x_797_, 1);
lean_inc_ref(v_code_796_);
v___x_798_ = l_Lean_Compiler_LCNF_Closure_collectCode(v_code_796_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
v___y_788_ = v___x_798_;
goto v___jp_787_;
}
else
{
v___y_788_ = v___x_797_;
goto v___jp_787_;
}
}
else
{
lean_object* v_code_799_; lean_object* v___x_800_; 
v_code_799_ = lean_ctor_get(v___x_794_, 0);
lean_inc_ref(v_code_799_);
v___x_800_ = l_Lean_Compiler_LCNF_Closure_collectCode(v_code_799_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
v___y_788_ = v___x_800_;
goto v___jp_787_;
}
}
else
{
lean_object* v___x_801_; 
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v_b_779_);
return v___x_801_;
}
v___jp_787_:
{
if (lean_obj_tag(v___y_788_) == 0)
{
lean_object* v_a_789_; size_t v___x_790_; size_t v___x_791_; 
v_a_789_ = lean_ctor_get(v___y_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___y_788_, 1);
v___x_790_ = ((size_t)1ULL);
v___x_791_ = lean_usize_add(v_i_777_, v___x_790_);
v_i_777_ = v___x_791_;
v_b_779_ = v_a_789_;
goto _start;
}
else
{
return v___y_788_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_776_ = stack[0].m_obj;
size_t v_i_777_ = stack[1].m_num;
size_t v_stop_778_ = stack[2].m_num;
lean_object* v_b_779_ = stack[3].m_obj;
lean_object* v___y_780_ = stack[4].m_obj;
lean_object* v___y_781_ = stack[5].m_obj;
lean_object* v___y_782_ = stack[6].m_obj;
lean_object* v___y_783_ = stack[7].m_obj;
lean_object* v___y_784_ = stack[8].m_obj;
lean_object* v___y_785_ = stack[9].m_obj;
lean_object* v_res_802_;
v_res_802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11(v_as_776_, v_i_777_, v_stop_778_, v_b_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
stack->m_obj
 = v_res_802_;
}
lean_object* l_Lean_Compiler_LCNF_Closure_collectCode(lean_object* v_c_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_decl_812_; lean_object* v_k_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; 
switch(lean_obj_tag(v_c_803_))
{
case 0:
{
lean_object* v_decl_822_; lean_object* v_k_823_; lean_object* v_type_824_; lean_object* v_value_825_; lean_object* v___x_826_; 
v_decl_822_ = lean_ctor_get(v_c_803_, 0);
lean_inc_ref(v_decl_822_);
v_k_823_ = lean_ctor_get(v_c_803_, 1);
lean_inc_ref(v_k_823_);
lean_dec_ref_known(v_c_803_, 2);
v_type_824_ = lean_ctor_get(v_decl_822_, 2);
lean_inc_ref(v_type_824_);
v_value_825_ = lean_ctor_get(v_decl_822_, 3);
lean_inc(v_value_825_);
lean_dec_ref(v_decl_822_);
v___x_826_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_824_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v___x_827_; 
lean_dec_ref_known(v___x_826_, 1);
v___x_827_ = l_Lean_Compiler_LCNF_Closure_collectLetValue(v_value_825_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_dec_ref_known(v___x_827_, 1);
v_c_803_ = v_k_823_;
goto _start;
}
else
{
lean_dec_ref(v_k_823_);
return v___x_827_;
}
}
else
{
lean_dec(v_value_825_);
lean_dec_ref(v_k_823_);
return v___x_826_;
}
}
case 3:
{
lean_object* v_args_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v_args_829_ = lean_ctor_get(v_c_803_, 1);
lean_inc_ref(v_args_829_);
lean_dec_ref_known(v_c_803_, 2);
v___x_830_ = lean_unsigned_to_nat(0u);
v___x_831_ = lean_array_get_size(v_args_829_);
v___x_832_ = lean_box(0);
v___x_833_ = lean_nat_dec_lt(v___x_830_, v___x_831_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
lean_dec_ref(v_args_829_);
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
return v___x_834_;
}
else
{
uint8_t v___x_835_; 
v___x_835_ = lean_nat_dec_le(v___x_831_, v___x_831_);
if (v___x_835_ == 0)
{
if (v___x_833_ == 0)
{
lean_object* v___x_836_; 
lean_dec_ref(v_args_829_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_832_);
return v___x_836_;
}
else
{
size_t v___x_837_; size_t v___x_838_; lean_object* v___x_839_; 
v___x_837_ = ((size_t)0ULL);
v___x_838_ = lean_usize_of_nat(v___x_831_);
v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_829_, v___x_837_, v___x_838_, v___x_832_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
lean_dec_ref(v_args_829_);
return v___x_839_;
}
}
else
{
size_t v___x_840_; size_t v___x_841_; lean_object* v___x_842_; 
v___x_840_ = ((size_t)0ULL);
v___x_841_ = lean_usize_of_nat(v___x_831_);
v___x_842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_829_, v___x_840_, v___x_841_, v___x_832_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
lean_dec_ref(v_args_829_);
return v___x_842_;
}
}
}
case 4:
{
lean_object* v_cases_843_; lean_object* v_resultType_844_; lean_object* v_discr_845_; lean_object* v_alts_846_; lean_object* v___x_847_; 
v_cases_843_ = lean_ctor_get(v_c_803_, 0);
lean_inc_ref(v_cases_843_);
lean_dec_ref_known(v_c_803_, 1);
v_resultType_844_ = lean_ctor_get(v_cases_843_, 1);
lean_inc_ref(v_resultType_844_);
v_discr_845_ = lean_ctor_get(v_cases_843_, 2);
lean_inc(v_discr_845_);
v_alts_846_ = lean_ctor_get(v_cases_843_, 3);
lean_inc_ref(v_alts_846_);
lean_dec_ref(v_cases_843_);
v___x_847_ = l_Lean_Compiler_LCNF_Closure_collectType(v_resultType_844_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v___x_848_; 
lean_dec_ref_known(v___x_847_, 1);
v___x_848_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v_discr_845_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_869_; 
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_869_ == 0)
{
lean_object* v_unused_870_; 
v_unused_870_ = lean_ctor_get(v___x_848_, 0);
lean_dec(v_unused_870_);
v___x_850_ = v___x_848_;
v_isShared_851_ = v_isSharedCheck_869_;
goto v_resetjp_849_;
}
else
{
lean_dec(v___x_848_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_869_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_852_ = lean_unsigned_to_nat(0u);
v___x_853_ = lean_array_get_size(v_alts_846_);
v___x_854_ = lean_box(0);
v___x_855_ = lean_nat_dec_lt(v___x_852_, v___x_853_);
if (v___x_855_ == 0)
{
lean_object* v___x_857_; 
lean_dec_ref(v_alts_846_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_854_);
v___x_857_ = v___x_850_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_854_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
else
{
uint8_t v___x_859_; 
v___x_859_ = lean_nat_dec_le(v___x_853_, v___x_853_);
if (v___x_859_ == 0)
{
if (v___x_855_ == 0)
{
lean_object* v___x_861_; 
lean_dec_ref(v_alts_846_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_854_);
v___x_861_ = v___x_850_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_854_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
else
{
size_t v___x_863_; size_t v___x_864_; lean_object* v___x_865_; 
lean_del_object(v___x_850_);
v___x_863_ = ((size_t)0ULL);
v___x_864_ = lean_usize_of_nat(v___x_853_);
v___x_865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11(v_alts_846_, v___x_863_, v___x_864_, v___x_854_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
lean_dec_ref(v_alts_846_);
return v___x_865_;
}
}
else
{
size_t v___x_866_; size_t v___x_867_; lean_object* v___x_868_; 
lean_del_object(v___x_850_);
v___x_866_ = ((size_t)0ULL);
v___x_867_ = lean_usize_of_nat(v___x_853_);
v___x_868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11(v_alts_846_, v___x_866_, v___x_867_, v___x_854_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
lean_dec_ref(v_alts_846_);
return v___x_868_;
}
}
}
}
else
{
lean_dec_ref(v_alts_846_);
return v___x_848_;
}
}
else
{
lean_dec_ref(v_alts_846_);
lean_dec(v_discr_845_);
return v___x_847_;
}
}
case 5:
{
lean_object* v_fvarId_871_; lean_object* v___x_872_; 
v_fvarId_871_ = lean_ctor_get(v_c_803_, 0);
lean_inc(v_fvarId_871_);
lean_dec_ref_known(v_c_803_, 1);
v___x_872_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v_fvarId_871_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
return v___x_872_;
}
case 6:
{
lean_object* v_type_873_; lean_object* v___x_874_; 
v_type_873_ = lean_ctor_get(v_c_803_, 0);
lean_inc_ref(v_type_873_);
lean_dec_ref_known(v_c_803_, 1);
v___x_874_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_873_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
return v___x_874_;
}
default: 
{
lean_object* v_decl_875_; lean_object* v_k_876_; 
v_decl_875_ = lean_ctor_get(v_c_803_, 0);
lean_inc_ref(v_decl_875_);
v_k_876_ = lean_ctor_get(v_c_803_, 1);
lean_inc_ref(v_k_876_);
lean_dec_ref(v_c_803_);
v_decl_812_ = v_decl_875_;
v_k_813_ = v_k_876_;
v___y_814_ = v_a_804_;
v___y_815_ = v_a_805_;
v___y_816_ = v_a_806_;
v___y_817_ = v_a_807_;
v___y_818_ = v_a_808_;
v___y_819_ = v_a_809_;
goto v___jp_811_;
}
}
v___jp_811_:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_Compiler_LCNF_Closure_collectFunDecl(v_decl_812_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_dec_ref_known(v___x_820_, 1);
v_c_803_ = v_k_813_;
v_a_804_ = v___y_814_;
v_a_805_ = v___y_815_;
v_a_806_ = v___y_816_;
v_a_807_ = v___y_817_;
v_a_808_ = v___y_818_;
v_a_809_ = v___y_819_;
goto _start;
}
else
{
lean_dec_ref(v_k_813_);
return v___x_820_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Closure_collectCode_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_803_ = stack[0].m_obj;
lean_object* v_a_804_ = stack[1].m_obj;
lean_object* v_a_805_ = stack[2].m_obj;
lean_object* v_a_806_ = stack[3].m_obj;
lean_object* v_a_807_ = stack[4].m_obj;
lean_object* v_a_808_ = stack[5].m_obj;
lean_object* v_a_809_ = stack[6].m_obj;
lean_object* v_res_877_;
v_res_877_ = l_Lean_Compiler_LCNF_Closure_collectCode(v_c_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
stack->m_obj
 = v_res_877_;
}
lean_object* l_Lean_Compiler_LCNF_Closure_collectFunDecl(lean_object* v_decl_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_params_886_; lean_object* v_type_887_; lean_object* v_value_888_; lean_object* v___x_889_; 
v_params_886_ = lean_ctor_get(v_decl_878_, 2);
lean_inc_ref(v_params_886_);
v_type_887_ = lean_ctor_get(v_decl_878_, 3);
lean_inc_ref(v_type_887_);
v_value_888_ = lean_ctor_get(v_decl_878_, 4);
lean_inc_ref(v_value_888_);
lean_dec_ref(v_decl_878_);
v___x_889_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_887_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v___x_890_; 
lean_dec_ref_known(v___x_889_, 1);
v___x_890_ = l_Lean_Compiler_LCNF_Closure_collectParams(v_params_886_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
lean_dec_ref(v_params_886_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v___x_891_; 
lean_dec_ref_known(v___x_890_, 1);
v___x_891_ = l_Lean_Compiler_LCNF_Closure_collectCode(v_value_888_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
return v___x_891_;
}
else
{
lean_dec_ref(v_value_888_);
return v___x_890_;
}
}
else
{
lean_dec_ref(v_value_888_);
lean_dec_ref(v_params_886_);
return v___x_889_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Closure_collectFunDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_878_ = stack[0].m_obj;
lean_object* v_a_879_ = stack[1].m_obj;
lean_object* v_a_880_ = stack[2].m_obj;
lean_object* v_a_881_ = stack[3].m_obj;
lean_object* v_a_882_ = stack[4].m_obj;
lean_object* v_a_883_ = stack[5].m_obj;
lean_object* v_a_884_ = stack[6].m_obj;
lean_object* v_res_892_;
v_res_892_ = l_Lean_Compiler_LCNF_Closure_collectFunDecl(v_decl_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
stack->m_obj
 = v_res_892_;
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_896_ = ((lean_object*)(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2));
v___x_897_ = lean_unsigned_to_nat(10u);
v___x_898_ = lean_unsigned_to_nat(149u);
v___x_899_ = ((lean_object*)(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1));
v___x_900_ = ((lean_object*)(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__0));
v___x_901_ = l_mkPanicMessageWithDecl(v___x_900_, v___x_899_, v___x_898_, v___x_897_, v___x_896_);
return v___x_901_;
}
}
lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar(lean_object* v_fvarId_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_910_; lean_object* v_visited_911_; uint8_t v___x_912_; 
v___x_910_ = lean_st_ref_get(v_a_904_);
v_visited_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc_ref(v_visited_911_);
lean_dec(v___x_910_);
v___x_912_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg(v_visited_911_, v_fvarId_902_);
lean_dec_ref(v_visited_911_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; 
lean_inc(v_fvarId_902_);
v___x_913_ = l_Lean_Compiler_LCNF_Closure_markVisited___redArg(v_fvarId_902_, v_a_904_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_1102_; 
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_1102_ == 0)
{
lean_object* v_unused_1103_; 
v_unused_1103_ = lean_ctor_get(v___x_913_, 0);
lean_dec(v_unused_1103_);
v___x_915_ = v___x_913_;
v_isShared_916_ = v_isSharedCheck_1102_;
goto v_resetjp_914_;
}
else
{
lean_dec(v___x_913_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_1102_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v_inScope_917_; lean_object* v_abstract_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v_inScope_917_ = lean_ctor_get(v_a_903_, 0);
v_abstract_918_ = lean_ctor_get(v_a_903_, 1);
lean_inc_ref(v_inScope_917_);
lean_inc(v_fvarId_902_);
v___x_919_ = lean_apply_1(v_inScope_917_, v_fvarId_902_);
v___x_920_ = lean_unbox(v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_923_; 
lean_dec(v_fvarId_902_);
v___x_921_ = lean_box(0);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_921_);
v___x_923_ = v___x_915_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
else
{
uint8_t v___x_925_; lean_object* v___x_926_; 
lean_del_object(v___x_915_);
v___x_925_ = 0;
v___x_926_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_925_, v_fvarId_902_, v_a_906_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_1093_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_929_ = v___x_926_;
v_isShared_930_ = v_isSharedCheck_1093_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_926_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_1093_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
if (lean_obj_tag(v_a_927_) == 1)
{
lean_object* v_val_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_984_; 
lean_dec(v_fvarId_902_);
v_val_931_ = lean_ctor_get(v_a_927_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v_a_927_);
if (v_isSharedCheck_984_ == 0)
{
v___x_933_ = v_a_927_;
v_isShared_934_ = v_isSharedCheck_984_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_val_931_);
lean_dec(v_a_927_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_984_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_fvarId_935_; lean_object* v_binderName_936_; lean_object* v_type_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v_fvarId_935_ = lean_ctor_get(v_val_931_, 0);
v_binderName_936_ = lean_ctor_get(v_val_931_, 1);
v_type_937_ = lean_ctor_get(v_val_931_, 3);
lean_inc_ref(v_abstract_918_);
lean_inc(v_fvarId_935_);
v___x_938_ = lean_apply_1(v_abstract_918_, v_fvarId_935_);
v___x_939_ = lean_unbox(v___x_938_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; 
lean_del_object(v___x_929_);
lean_inc(v_val_931_);
v___x_940_ = l_Lean_Compiler_LCNF_Closure_collectFunDecl(v_val_931_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_964_; 
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; 
v_unused_965_ = lean_ctor_get(v___x_940_, 0);
lean_dec(v_unused_965_);
v___x_942_ = v___x_940_;
v_isShared_943_ = v_isSharedCheck_964_;
goto v_resetjp_941_;
}
else
{
lean_dec(v___x_940_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_964_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v_visited_945_; lean_object* v_params_946_; lean_object* v_decls_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_963_; 
v___x_944_ = lean_st_ref_take(v_a_904_);
v_visited_945_ = lean_ctor_get(v___x_944_, 0);
v_params_946_ = lean_ctor_get(v___x_944_, 1);
v_decls_947_ = lean_ctor_get(v___x_944_, 2);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_963_ == 0)
{
v___x_949_ = v___x_944_;
v_isShared_950_ = v_isSharedCheck_963_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_decls_947_);
lean_inc(v_params_946_);
lean_inc(v_visited_945_);
lean_dec(v___x_944_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_963_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_951_ = lean_box(0);
if (v_isShared_934_ == 0)
{
v___x_953_ = v___x_933_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_val_931_);
v___x_953_ = v_reuseFailAlloc_962_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_954_ = lean_array_push(v_decls_947_, v___x_953_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 2, v___x_954_);
v___x_956_ = v___x_949_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_visited_945_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_params_946_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v___x_954_);
v___x_956_ = v_reuseFailAlloc_961_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_957_ = lean_st_ref_put(v_a_904_, v___x_956_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v___x_951_);
v___x_959_ = v___x_942_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_951_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_933_);
lean_dec(v_val_931_);
return v___x_940_;
}
}
else
{
lean_object* v___x_966_; lean_object* v_visited_967_; lean_object* v_params_968_; lean_object* v_decls_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_983_; 
lean_inc_ref(v_type_937_);
lean_inc(v_binderName_936_);
lean_inc(v_fvarId_935_);
lean_del_object(v___x_933_);
lean_dec(v_val_931_);
v___x_966_ = lean_st_ref_take(v_a_904_);
v_visited_967_ = lean_ctor_get(v___x_966_, 0);
v_params_968_ = lean_ctor_get(v___x_966_, 1);
v_decls_969_ = lean_ctor_get(v___x_966_, 2);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_983_ == 0)
{
v___x_971_ = v___x_966_;
v_isShared_972_ = v_isSharedCheck_983_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_decls_969_);
lean_inc(v_params_968_);
lean_inc(v_visited_967_);
lean_dec(v___x_966_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_983_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_973_ = lean_box(0);
v___x_974_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_974_, 0, v_fvarId_935_);
lean_ctor_set(v___x_974_, 1, v_binderName_936_);
lean_ctor_set(v___x_974_, 2, v_type_937_);
lean_ctor_set_uint8(v___x_974_, sizeof(void*)*3, v___x_912_);
v___x_975_ = lean_array_push(v_params_968_, v___x_974_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 1, v___x_975_);
v___x_977_ = v___x_971_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_visited_967_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v_decls_969_);
v___x_977_ = v_reuseFailAlloc_982_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = lean_st_ref_put(v_a_904_, v___x_977_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_973_);
v___x_980_ = v___x_929_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_973_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
}
else
{
lean_object* v___x_985_; 
lean_del_object(v___x_929_);
lean_dec(v_a_927_);
v___x_985_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v___x_925_, v_fvarId_902_, v_a_906_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_985_, 1);
if (lean_obj_tag(v_a_986_) == 1)
{
lean_object* v_val_987_; lean_object* v_type_988_; lean_object* v___x_989_; 
lean_dec(v_fvarId_902_);
v_val_987_ = lean_ctor_get(v_a_986_, 0);
lean_inc(v_val_987_);
lean_dec_ref_known(v_a_986_, 1);
v_type_988_ = lean_ctor_get(v_val_987_, 2);
lean_inc_ref(v_type_988_);
v___x_989_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_988_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1010_; 
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1010_ == 0)
{
lean_object* v_unused_1011_; 
v_unused_1011_ = lean_ctor_get(v___x_989_, 0);
lean_dec(v_unused_1011_);
v___x_991_ = v___x_989_;
v_isShared_992_ = v_isSharedCheck_1010_;
goto v_resetjp_990_;
}
else
{
lean_dec(v___x_989_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1010_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v_visited_994_; lean_object* v_params_995_; lean_object* v_decls_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1009_; 
v___x_993_ = lean_st_ref_take(v_a_904_);
v_visited_994_ = lean_ctor_get(v___x_993_, 0);
v_params_995_ = lean_ctor_get(v___x_993_, 1);
v_decls_996_ = lean_ctor_get(v___x_993_, 2);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_998_ = v___x_993_;
v_isShared_999_ = v_isSharedCheck_1009_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_decls_996_);
lean_inc(v_params_995_);
lean_inc(v_visited_994_);
lean_dec(v___x_993_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1009_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_1000_ = lean_box(0);
v___x_1001_ = lean_array_push(v_params_995_, v_val_987_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 1, v___x_1001_);
v___x_1003_ = v___x_998_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_visited_994_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1008_, 2, v_decls_996_);
v___x_1003_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1004_ = lean_st_ref_put(v_a_904_, v___x_1003_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v___x_1000_);
v___x_1006_ = v___x_991_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1000_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
else
{
lean_dec(v_val_987_);
return v___x_989_;
}
}
else
{
lean_object* v___x_1012_; 
lean_dec(v_a_986_);
v___x_1012_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_925_, v_fvarId_902_, v_a_906_);
lean_dec(v_fvarId_902_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1012_, 1);
if (lean_obj_tag(v_a_1013_) == 1)
{
lean_object* v_val_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1074_; 
v_val_1014_ = lean_ctor_get(v_a_1013_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_a_1013_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1016_ = v_a_1013_;
v_isShared_1017_ = v_isSharedCheck_1074_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_val_1014_);
lean_dec(v_a_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1074_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v_fvarId_1018_; lean_object* v_binderName_1019_; lean_object* v_type_1020_; lean_object* v_value_1021_; lean_object* v___x_1022_; 
v_fvarId_1018_ = lean_ctor_get(v_val_1014_, 0);
v_binderName_1019_ = lean_ctor_get(v_val_1014_, 1);
v_type_1020_ = lean_ctor_get(v_val_1014_, 2);
v_value_1021_ = lean_ctor_get(v_val_1014_, 3);
lean_inc_ref(v_type_1020_);
v___x_1022_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_1020_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1072_; 
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1072_ == 0)
{
lean_object* v_unused_1073_; 
v_unused_1073_ = lean_ctor_get(v___x_1022_, 0);
lean_dec(v_unused_1073_);
v___x_1024_ = v___x_1022_;
v_isShared_1025_ = v_isSharedCheck_1072_;
goto v_resetjp_1023_;
}
else
{
lean_dec(v___x_1022_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1072_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; uint8_t v___x_1027_; 
lean_inc_ref(v_abstract_918_);
lean_inc(v_fvarId_1018_);
v___x_1026_ = lean_apply_1(v_abstract_918_, v_fvarId_1018_);
v___x_1027_ = lean_unbox(v___x_1026_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; 
lean_del_object(v___x_1024_);
lean_inc(v_value_1021_);
v___x_1028_ = l_Lean_Compiler_LCNF_Closure_collectLetValue(v_value_1021_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1052_; 
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; 
v_unused_1053_ = lean_ctor_get(v___x_1028_, 0);
lean_dec(v_unused_1053_);
v___x_1030_ = v___x_1028_;
v_isShared_1031_ = v_isSharedCheck_1052_;
goto v_resetjp_1029_;
}
else
{
lean_dec(v___x_1028_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1052_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; lean_object* v_visited_1033_; lean_object* v_params_1034_; lean_object* v_decls_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1051_; 
v___x_1032_ = lean_st_ref_take(v_a_904_);
v_visited_1033_ = lean_ctor_get(v___x_1032_, 0);
v_params_1034_ = lean_ctor_get(v___x_1032_, 1);
v_decls_1035_ = lean_ctor_get(v___x_1032_, 2);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1037_ = v___x_1032_;
v_isShared_1038_ = v_isSharedCheck_1051_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_decls_1035_);
lean_inc(v_params_1034_);
lean_inc(v_visited_1033_);
lean_dec(v___x_1032_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1051_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1039_ = lean_box(0);
if (v_isShared_1017_ == 0)
{
lean_ctor_set_tag(v___x_1016_, 0);
v___x_1041_ = v___x_1016_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_val_1014_);
v___x_1041_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1042_ = lean_array_push(v_decls_1035_, v___x_1041_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 2, v___x_1042_);
v___x_1044_ = v___x_1037_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_visited_1033_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_params_1034_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1045_ = lean_st_ref_put(v_a_904_, v___x_1044_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1039_);
v___x_1047_ = v___x_1030_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1039_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1016_);
lean_dec(v_val_1014_);
return v___x_1028_;
}
}
else
{
lean_object* v___x_1054_; lean_object* v_visited_1055_; lean_object* v_params_1056_; lean_object* v_decls_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1071_; 
lean_inc_ref(v_type_1020_);
lean_inc(v_binderName_1019_);
lean_inc(v_fvarId_1018_);
lean_del_object(v___x_1016_);
lean_dec(v_val_1014_);
v___x_1054_ = lean_st_ref_take(v_a_904_);
v_visited_1055_ = lean_ctor_get(v___x_1054_, 0);
v_params_1056_ = lean_ctor_get(v___x_1054_, 1);
v_decls_1057_ = lean_ctor_get(v___x_1054_, 2);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1059_ = v___x_1054_;
v_isShared_1060_ = v_isSharedCheck_1071_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_decls_1057_);
lean_inc(v_params_1056_);
lean_inc(v_visited_1055_);
lean_dec(v___x_1054_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1071_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1061_ = lean_box(0);
v___x_1062_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1062_, 0, v_fvarId_1018_);
lean_ctor_set(v___x_1062_, 1, v_binderName_1019_);
lean_ctor_set(v___x_1062_, 2, v_type_1020_);
lean_ctor_set_uint8(v___x_1062_, sizeof(void*)*3, v___x_912_);
v___x_1063_ = lean_array_push(v_params_1056_, v___x_1062_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 1, v___x_1063_);
v___x_1065_ = v___x_1059_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_visited_1055_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v_decls_1057_);
v___x_1065_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1066_ = lean_st_ref_put(v_a_904_, v___x_1065_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1061_);
v___x_1068_ = v___x_1024_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1061_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1016_);
lean_dec(v_val_1014_);
return v___x_1022_;
}
}
}
else
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec(v_a_1013_);
v___x_1075_ = lean_obj_once(&l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3, &l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3_once, _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3);
v___x_1076_ = l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5(v___x_1075_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
return v___x_1076_;
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
v_a_1077_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1012_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1012_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec(v_fvarId_902_);
v_a_1085_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_985_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_985_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_dec(v_fvarId_902_);
v_a_1094_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_926_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_926_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_902_);
return v___x_913_;
}
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_dec(v_fvarId_902_);
v___x_1104_ = lean_box(0);
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
return v___x_1105_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Closure_collectFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_902_ = stack[0].m_obj;
lean_object* v_a_903_ = stack[1].m_obj;
lean_object* v_a_904_ = stack[2].m_obj;
lean_object* v_a_905_ = stack[3].m_obj;
lean_object* v_a_906_ = stack[4].m_obj;
lean_object* v_a_907_ = stack[5].m_obj;
lean_object* v_a_908_ = stack[6].m_obj;
lean_object* v_res_1106_;
v_res_1106_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v_fvarId_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
stack->m_obj
 = v_res_1106_;
}
lean_object* l_Lean_Compiler_LCNF_Closure_collectType___lam__0(lean_object* v_e_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = l_Lean_Expr_fvarId_x21(v_e_1107_);
v___x_1116_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v___x_1115_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
return v___x_1116_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Closure_collectType___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1107_ = stack[0].m_obj;
lean_object* v___y_1108_ = stack[1].m_obj;
lean_object* v___y_1109_ = stack[2].m_obj;
lean_object* v___y_1110_ = stack[3].m_obj;
lean_object* v___y_1111_ = stack[4].m_obj;
lean_object* v___y_1112_ = stack[5].m_obj;
lean_object* v___y_1113_ = stack[6].m_obj;
lean_object* v_res_1117_;
v_res_1117_ = l_Lean_Compiler_LCNF_Closure_collectType___lam__0(v_e_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
stack->m_obj
 = v_res_1117_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectArg___boxed(lean_object* v_arg_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_Compiler_LCNF_Closure_collectArg(v_arg_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType___boxed(lean_object* v_type_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFunDecl___boxed(lean_object* v_decl_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_Compiler_LCNF_Closure_collectFunDecl(v_decl_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7___boxed(lean_object* v_as_1145_, lean_object* v_i_1146_, lean_object* v_stop_1147_, lean_object* v_b_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
size_t v_i_boxed_1156_; size_t v_stop_boxed_1157_; lean_object* v_res_1158_; 
v_i_boxed_1156_ = lean_unbox_usize(v_i_1146_);
lean_dec(v_i_1146_);
v_stop_boxed_1157_ = lean_unbox_usize(v_stop_1147_);
lean_dec(v_stop_1147_);
v_res_1158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_as_1145_, v_i_boxed_1156_, v_stop_boxed_1157_, v_b_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec_ref(v_as_1145_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0___boxed(lean_object* v_as_1159_, lean_object* v_i_1160_, lean_object* v_stop_1161_, lean_object* v_b_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
size_t v_i_boxed_1170_; size_t v_stop_boxed_1171_; lean_object* v_res_1172_; 
v_i_boxed_1170_ = lean_unbox_usize(v_i_1160_);
lean_dec(v_i_1160_);
v_stop_boxed_1171_ = lean_unbox_usize(v_stop_1161_);
lean_dec(v_stop_1161_);
v_res_1172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0(v_as_1159_, v_i_boxed_1170_, v_stop_boxed_1171_, v_b_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec_ref(v_as_1159_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectParams___boxed(lean_object* v_params_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_Compiler_LCNF_Closure_collectParams(v_params_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec_ref(v_params_1173_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11___boxed(lean_object* v_as_1182_, lean_object* v_i_1183_, lean_object* v_stop_1184_, lean_object* v_b_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
size_t v_i_boxed_1193_; size_t v_stop_boxed_1194_; lean_object* v_res_1195_; 
v_i_boxed_1193_ = lean_unbox_usize(v_i_1183_);
lean_dec(v_i_1183_);
v_stop_boxed_1194_ = lean_unbox_usize(v_stop_1184_);
lean_dec(v_stop_1184_);
v_res_1195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11(v_as_1182_, v_i_boxed_1193_, v_stop_boxed_1194_, v_b_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec_ref(v_as_1182_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectLetValue___boxed(lean_object* v_e_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_Compiler_LCNF_Closure_collectLetValue(v_e_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
lean_dec(v_a_1198_);
lean_dec_ref(v_a_1197_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectCode___boxed(lean_object* v_c_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_Compiler_LCNF_Closure_collectCode(v_c_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar___boxed(lean_object* v_fvarId_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v_fvarId_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
return v_res_1222_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4(lean_object* v_00_u03b2_1223_, lean_object* v_m_1224_, lean_object* v_a_1225_){
_start:
{
uint8_t v___x_1226_; 
v___x_1226_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg(v_m_1224_, v_a_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1224_ = stack[1].m_obj;
lean_object* v_a_1225_ = stack[2].m_obj;
uint8_t v_res_1227_;
v_res_1227_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4(lean_box(0), v_m_1224_, v_a_1225_);
stack->m_num = v_res_1227_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___boxed(lean_object* v_00_u03b2_1228_, lean_object* v_m_1229_, lean_object* v_a_1230_){
_start:
{
uint8_t v_res_1231_; lean_object* v_r_1232_; 
v_res_1231_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4(v_00_u03b2_1228_, v_m_1229_, v_a_1230_);
lean_dec(v_a_1230_);
lean_dec_ref(v_m_1229_);
v_r_1232_ = lean_box(v_res_1231_);
return v_r_1232_;
}
}
lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9(lean_object* v_e_1233_, lean_object* v_a_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg(v_e_1233_, v_a_1234_);
return v___x_1242_;
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1233_ = stack[0].m_obj;
lean_object* v_a_1234_ = stack[1].m_obj;
lean_object* v___y_1235_ = stack[2].m_obj;
lean_object* v___y_1236_ = stack[3].m_obj;
lean_object* v___y_1237_ = stack[4].m_obj;
lean_object* v___y_1238_ = stack[5].m_obj;
lean_object* v___y_1239_ = stack[6].m_obj;
lean_object* v___y_1240_ = stack[7].m_obj;
lean_object* v_res_1243_;
v_res_1243_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9(v_e_1233_, v_a_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
stack->m_obj
 = v_res_1243_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___boxed(lean_object* v_e_1244_, lean_object* v_a_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9(v_e_1244_, v_a_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v_a_1245_);
return v_res_1253_;
}
}
lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10(lean_object* v_e_1254_, lean_object* v_a_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg(v_e_1254_, v_a_1255_);
return v___x_1263_;
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1254_ = stack[0].m_obj;
lean_object* v_a_1255_ = stack[1].m_obj;
lean_object* v___y_1256_ = stack[2].m_obj;
lean_object* v___y_1257_ = stack[3].m_obj;
lean_object* v___y_1258_ = stack[4].m_obj;
lean_object* v___y_1259_ = stack[5].m_obj;
lean_object* v___y_1260_ = stack[6].m_obj;
lean_object* v___y_1261_ = stack[7].m_obj;
lean_object* v_res_1264_;
v_res_1264_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10(v_e_1254_, v_a_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
stack->m_obj
 = v_res_1264_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___boxed(lean_object* v_e_1265_, lean_object* v_a_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10(v_e_1265_, v_a_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v_a_1266_);
return v_res_1274_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14(lean_object* v_00_u03b2_1275_, lean_object* v_m_1276_, lean_object* v_a_1277_){
_start:
{
uint8_t v___x_1278_; 
v___x_1278_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg(v_m_1276_, v_a_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1276_ = stack[1].m_obj;
lean_object* v_a_1277_ = stack[2].m_obj;
uint8_t v_res_1279_;
v_res_1279_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14(lean_box(0), v_m_1276_, v_a_1277_);
stack->m_num = v_res_1279_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___boxed(lean_object* v_00_u03b2_1280_, lean_object* v_m_1281_, lean_object* v_a_1282_){
_start:
{
uint8_t v_res_1283_; lean_object* v_r_1284_; 
v_res_1283_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14(v_00_u03b2_1280_, v_m_1281_, v_a_1282_);
lean_dec_ref(v_a_1282_);
lean_dec_ref(v_m_1281_);
v_r_1284_ = lean_box(v_res_1283_);
return v_r_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15(lean_object* v_00_u03b2_1285_, lean_object* v_m_1286_, lean_object* v_a_1287_, lean_object* v_b_1288_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15___redArg(v_m_1286_, v_a_1287_, v_b_1288_);
return v___x_1289_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15(lean_object* v_00_u03b2_1290_, lean_object* v_a_1291_, lean_object* v_x_1292_){
_start:
{
uint8_t v___x_1293_; 
v___x_1293_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(v_a_1291_, v_x_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1291_ = stack[1].m_obj;
lean_object* v_x_1292_ = stack[2].m_obj;
uint8_t v_res_1294_;
v_res_1294_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15(lean_box(0), v_a_1291_, v_x_1292_);
stack->m_num = v_res_1294_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___boxed(lean_object* v_00_u03b2_1295_, lean_object* v_a_1296_, lean_object* v_x_1297_){
_start:
{
uint8_t v_res_1298_; lean_object* v_r_1299_; 
v_res_1298_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15(v_00_u03b2_1295_, v_a_1296_, v_x_1297_);
lean_dec(v_x_1297_);
lean_dec_ref(v_a_1296_);
v_r_1299_ = lean_box(v_res_1298_);
return v_r_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17(lean_object* v_00_u03b2_1300_, lean_object* v_data_1301_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17___redArg(v_data_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18(lean_object* v_00_u03b2_1303_, lean_object* v_i_1304_, lean_object* v_source_1305_, lean_object* v_target_1306_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18___redArg(v_i_1304_, v_source_1305_, v_target_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_1308_, lean_object* v_x_1309_, lean_object* v_x_1310_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18_spec__19___redArg(v_x_1309_, v_x_1310_);
return v___x_1311_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(lean_object* v_k_1312_, lean_object* v_t_1313_){
_start:
{
if (lean_obj_tag(v_t_1313_) == 0)
{
lean_object* v_k_1314_; lean_object* v_l_1315_; lean_object* v_r_1316_; uint8_t v___x_1317_; 
v_k_1314_ = lean_ctor_get(v_t_1313_, 1);
v_l_1315_ = lean_ctor_get(v_t_1313_, 3);
v_r_1316_ = lean_ctor_get(v_t_1313_, 4);
v___x_1317_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1312_, v_k_1314_);
switch(v___x_1317_)
{
case 0:
{
v_t_1313_ = v_l_1315_;
goto _start;
}
case 1:
{
uint8_t v___x_1319_; 
v___x_1319_ = 1;
return v___x_1319_;
}
default: 
{
v_t_1313_ = v_r_1316_;
goto _start;
}
}
}
else
{
uint8_t v___x_1321_; 
v___x_1321_ = 0;
return v___x_1321_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1312_ = stack[0].m_obj;
lean_object* v_t_1313_ = stack[1].m_obj;
uint8_t v_res_1322_;
v_res_1322_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(v_k_1312_, v_t_1313_);
stack->m_num = v_res_1322_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg___boxed(lean_object* v_k_1323_, lean_object* v_t_1324_){
_start:
{
uint8_t v_res_1325_; lean_object* v_r_1326_; 
v_res_1325_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(v_k_1323_, v_t_1324_);
lean_dec(v_t_1324_);
lean_dec(v_k_1323_);
v_r_1326_ = lean_box(v_res_1325_);
return v_r_1326_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(lean_object* v_a_1327_, lean_object* v_as_1328_, size_t v_i_1329_, size_t v_stop_1330_, lean_object* v_b_1331_){
_start:
{
lean_object* v___y_1333_; uint8_t v___x_1337_; 
v___x_1337_ = lean_usize_dec_eq(v_i_1329_, v_stop_1330_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1338_ = lean_array_uget_borrowed(v_as_1328_, v_i_1329_);
v___x_1339_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v___x_1338_);
v___x_1340_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(v___x_1339_, v_a_1327_);
lean_dec(v___x_1339_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; 
lean_inc(v___x_1338_);
v___x_1341_ = lean_array_push(v_b_1331_, v___x_1338_);
v___y_1333_ = v___x_1341_;
goto v___jp_1332_;
}
else
{
v___y_1333_ = v_b_1331_;
goto v___jp_1332_;
}
}
else
{
return v_b_1331_;
}
v___jp_1332_:
{
size_t v___x_1334_; size_t v___x_1335_; 
v___x_1334_ = ((size_t)1ULL);
v___x_1335_ = lean_usize_add(v_i_1329_, v___x_1334_);
v_i_1329_ = v___x_1335_;
v_b_1331_ = v___y_1333_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1327_ = stack[0].m_obj;
lean_object* v_as_1328_ = stack[1].m_obj;
size_t v_i_1329_ = stack[2].m_num;
size_t v_stop_1330_ = stack[3].m_num;
lean_object* v_b_1331_ = stack[4].m_obj;
lean_object* v_res_1342_;
v_res_1342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(v_a_1327_, v_as_1328_, v_i_1329_, v_stop_1330_, v_b_1331_);
stack->m_obj
 = v_res_1342_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2___boxed(lean_object* v_a_1343_, lean_object* v_as_1344_, lean_object* v_i_1345_, lean_object* v_stop_1346_, lean_object* v_b_1347_){
_start:
{
size_t v_i_boxed_1348_; size_t v_stop_boxed_1349_; lean_object* v_res_1350_; 
v_i_boxed_1348_ = lean_unbox_usize(v_i_1345_);
lean_dec(v_i_1345_);
v_stop_boxed_1349_ = lean_unbox_usize(v_stop_1346_);
lean_dec(v_stop_1346_);
v_res_1350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(v_a_1343_, v_as_1344_, v_i_boxed_1348_, v_stop_boxed_1349_, v_b_1347_);
lean_dec_ref(v_as_1344_);
lean_dec(v_a_1343_);
return v_res_1350_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(lean_object* v_as_1351_, size_t v_sz_1352_, size_t v_i_1353_, lean_object* v_b_1354_){
_start:
{
uint8_t v___x_1356_; 
v___x_1356_ = lean_usize_dec_lt(v_i_1353_, v_sz_1352_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1357_, 0, v_b_1354_);
return v___x_1357_;
}
else
{
lean_object* v_a_1358_; lean_object* v_fvarId_1359_; lean_object* v___x_1360_; size_t v___x_1361_; size_t v___x_1362_; 
v_a_1358_ = lean_array_uget_borrowed(v_as_1351_, v_i_1353_);
v_fvarId_1359_ = lean_ctor_get(v_a_1358_, 0);
lean_inc(v_fvarId_1359_);
v___x_1360_ = l_Lean_FVarIdSet_insert(v_b_1354_, v_fvarId_1359_);
v___x_1361_ = ((size_t)1ULL);
v___x_1362_ = lean_usize_add(v_i_1353_, v___x_1361_);
v_i_1353_ = v___x_1362_;
v_b_1354_ = v___x_1360_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1351_ = stack[0].m_obj;
size_t v_sz_1352_ = stack[1].m_num;
size_t v_i_1353_ = stack[2].m_num;
lean_object* v_b_1354_ = stack[3].m_obj;
lean_object* v_res_1364_;
v_res_1364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(v_as_1351_, v_sz_1352_, v_i_1353_, v_b_1354_);
stack->m_obj
 = v_res_1364_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg___boxed(lean_object* v_as_1365_, lean_object* v_sz_1366_, lean_object* v_i_1367_, lean_object* v_b_1368_, lean_object* v___y_1369_){
_start:
{
size_t v_sz_boxed_1370_; size_t v_i_boxed_1371_; lean_object* v_res_1372_; 
v_sz_boxed_1370_ = lean_unbox_usize(v_sz_1366_);
lean_dec(v_sz_1366_);
v_i_boxed_1371_ = lean_unbox_usize(v_i_1367_);
lean_dec(v_i_1367_);
v_res_1372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(v_as_1365_, v_sz_boxed_1370_, v_i_boxed_1371_, v_b_1368_);
lean_dec_ref(v_as_1365_);
return v_res_1372_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = ((lean_object*)(l_Lean_Compiler_LCNF_Closure_run___redArg___closed__0));
v___x_1376_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_1377_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
lean_ctor_set(v___x_1377_, 1, v___x_1375_);
lean_ctor_set(v___x_1377_, 2, v___x_1375_);
return v___x_1377_;
}
}
lean_object* l_Lean_Compiler_LCNF_Closure_run___redArg(lean_object* v_x_1378_, lean_object* v_inScope_1379_, lean_object* v_abstract_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1386_ = lean_box(1);
v___x_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1387_, 0, v_inScope_1379_);
lean_ctor_set(v___x_1387_, 1, v_abstract_1380_);
v___x_1388_ = lean_unsigned_to_nat(0u);
v___x_1389_ = ((lean_object*)(l_Lean_Compiler_LCNF_Closure_run___redArg___closed__0));
v___x_1390_ = lean_obj_once(&l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1, &l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1);
v___x_1391_ = lean_st_mk_ref(v___x_1390_);
lean_inc(v_a_1384_);
lean_inc_ref(v_a_1383_);
lean_inc(v_a_1382_);
lean_inc_ref(v_a_1381_);
lean_inc(v___x_1391_);
v___x_1392_ = lean_apply_7(v_x_1378_, v___x_1387_, v___x_1391_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, lean_box(0));
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1394_; lean_object* v_params_1395_; lean_object* v_decls_1396_; size_t v_sz_1397_; size_t v___x_1398_; lean_object* v___x_1399_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref_known(v___x_1392_, 1);
v___x_1394_ = lean_st_ref_get(v___x_1391_);
lean_dec(v___x_1391_);
v_params_1395_ = lean_ctor_get(v___x_1394_, 1);
lean_inc_ref(v_params_1395_);
v_decls_1396_ = lean_ctor_get(v___x_1394_, 2);
lean_inc_ref(v_decls_1396_);
lean_dec(v___x_1394_);
v_sz_1397_ = lean_array_size(v_params_1395_);
v___x_1398_ = ((size_t)0ULL);
v___x_1399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(v_params_1395_, v_sz_1397_, v___x_1398_, v___x_1386_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1418_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1418_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1418_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___y_1405_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1411_ = lean_array_get_size(v_decls_1396_);
v___x_1412_ = lean_nat_dec_lt(v___x_1388_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_dec(v_a_1400_);
lean_dec_ref(v_decls_1396_);
v___y_1405_ = v___x_1389_;
goto v___jp_1404_;
}
else
{
uint8_t v___x_1413_; 
v___x_1413_ = lean_nat_dec_le(v___x_1411_, v___x_1411_);
if (v___x_1413_ == 0)
{
if (v___x_1412_ == 0)
{
lean_dec(v_a_1400_);
lean_dec_ref(v_decls_1396_);
v___y_1405_ = v___x_1389_;
goto v___jp_1404_;
}
else
{
size_t v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_usize_of_nat(v___x_1411_);
v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(v_a_1400_, v_decls_1396_, v___x_1398_, v___x_1414_, v___x_1389_);
lean_dec_ref(v_decls_1396_);
lean_dec(v_a_1400_);
v___y_1405_ = v___x_1415_;
goto v___jp_1404_;
}
}
else
{
size_t v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_usize_of_nat(v___x_1411_);
v___x_1417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(v_a_1400_, v_decls_1396_, v___x_1398_, v___x_1416_, v___x_1389_);
lean_dec_ref(v_decls_1396_);
lean_dec(v_a_1400_);
v___y_1405_ = v___x_1417_;
goto v___jp_1404_;
}
}
v___jp_1404_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1406_, 0, v_params_1395_);
lean_ctor_set(v___x_1406_, 1, v___y_1405_);
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v_a_1393_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v___x_1407_);
v___x_1409_ = v___x_1402_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec_ref(v_decls_1396_);
lean_dec_ref(v_params_1395_);
lean_dec(v_a_1393_);
v_a_1419_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1399_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1399_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_dec(v___x_1391_);
v_a_1427_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1392_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1392_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Closure_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1378_ = stack[0].m_obj;
lean_object* v_inScope_1379_ = stack[1].m_obj;
lean_object* v_abstract_1380_ = stack[2].m_obj;
lean_object* v_a_1381_ = stack[3].m_obj;
lean_object* v_a_1382_ = stack[4].m_obj;
lean_object* v_a_1383_ = stack[5].m_obj;
lean_object* v_a_1384_ = stack[6].m_obj;
lean_object* v_res_1435_;
v_res_1435_ = l_Lean_Compiler_LCNF_Closure_run___redArg(v_x_1378_, v_inScope_1379_, v_abstract_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
stack->m_obj
 = v_res_1435_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run___redArg___boxed(lean_object* v_x_1436_, lean_object* v_inScope_1437_, lean_object* v_abstract_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_Compiler_LCNF_Closure_run___redArg(v_x_1436_, v_inScope_1437_, v_abstract_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
return v_res_1444_;
}
}
lean_object* l_Lean_Compiler_LCNF_Closure_run(lean_object* v_00_u03b1_1445_, lean_object* v_x_1446_, lean_object* v_inScope_1447_, lean_object* v_abstract_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_Compiler_LCNF_Closure_run___redArg(v_x_1446_, v_inScope_1447_, v_abstract_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
return v___x_1454_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Closure_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1446_ = stack[1].m_obj;
lean_object* v_inScope_1447_ = stack[2].m_obj;
lean_object* v_abstract_1448_ = stack[3].m_obj;
lean_object* v_a_1449_ = stack[4].m_obj;
lean_object* v_a_1450_ = stack[5].m_obj;
lean_object* v_a_1451_ = stack[6].m_obj;
lean_object* v_a_1452_ = stack[7].m_obj;
lean_object* v_res_1455_;
v_res_1455_ = l_Lean_Compiler_LCNF_Closure_run(lean_box(0), v_x_1446_, v_inScope_1447_, v_abstract_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
stack->m_obj
 = v_res_1455_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run___boxed(lean_object* v_00_u03b1_1456_, lean_object* v_x_1457_, lean_object* v_inScope_1458_, lean_object* v_abstract_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_Compiler_LCNF_Closure_run(v_00_u03b1_1456_, v_x_1457_, v_inScope_1458_, v_abstract_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1460_);
return v_res_1465_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0(lean_object* v_as_1466_, size_t v_sz_1467_, size_t v_i_1468_, lean_object* v_b_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(v_as_1466_, v_sz_1467_, v_i_1468_, v_b_1469_);
return v___x_1475_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1466_ = stack[0].m_obj;
size_t v_sz_1467_ = stack[1].m_num;
size_t v_i_1468_ = stack[2].m_num;
lean_object* v_b_1469_ = stack[3].m_obj;
lean_object* v___y_1470_ = stack[4].m_obj;
lean_object* v___y_1471_ = stack[5].m_obj;
lean_object* v___y_1472_ = stack[6].m_obj;
lean_object* v___y_1473_ = stack[7].m_obj;
lean_object* v_res_1476_;
v_res_1476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0(v_as_1466_, v_sz_1467_, v_i_1468_, v_b_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
stack->m_obj
 = v_res_1476_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___boxed(lean_object* v_as_1477_, lean_object* v_sz_1478_, lean_object* v_i_1479_, lean_object* v_b_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
size_t v_sz_boxed_1486_; size_t v_i_boxed_1487_; lean_object* v_res_1488_; 
v_sz_boxed_1486_ = lean_unbox_usize(v_sz_1478_);
lean_dec(v_sz_1478_);
v_i_boxed_1487_ = lean_unbox_usize(v_i_1479_);
lean_dec(v_i_1479_);
v_res_1488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0(v_as_1477_, v_sz_boxed_1486_, v_i_boxed_1487_, v_b_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec_ref(v_as_1477_);
return v_res_1488_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1(lean_object* v_00_u03b2_1489_, lean_object* v_k_1490_, lean_object* v_t_1491_){
_start:
{
uint8_t v___x_1492_; 
v___x_1492_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(v_k_1490_, v_t_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1490_ = stack[1].m_obj;
lean_object* v_t_1491_ = stack[2].m_obj;
uint8_t v_res_1493_;
v_res_1493_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1(lean_box(0), v_k_1490_, v_t_1491_);
stack->m_num = v_res_1493_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___boxed(lean_object* v_00_u03b2_1494_, lean_object* v_k_1495_, lean_object* v_t_1496_){
_start:
{
uint8_t v_res_1497_; lean_object* v_r_1498_; 
v_res_1497_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1(v_00_u03b2_1494_, v_k_1495_, v_t_1496_);
lean_dec(v_t_1496_);
lean_dec(v_k_1495_);
v_r_1498_ = lean_box(v_res_1497_);
return v_r_1498_;
}
}
lean_object* runtime_initialize_Lean_Util_ForEachExprWhere(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Closure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Util_ForEachExprWhere(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Closure(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_ForEachExprWhere(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Closure(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_ForEachExprWhere(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Closure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Closure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Closure(builtin);
}
#ifdef __cplusplus
}
#endif
