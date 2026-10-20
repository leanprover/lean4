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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg(lean_object* v_a_50_, lean_object* v_x_51_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg___boxed(lean_object* v_a_57_, lean_object* v_x_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg(v_a_57_, v_x_58_);
lean_dec(v_x_58_);
lean_dec(v_a_57_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0___redArg(lean_object* v_m_61_, lean_object* v_a_62_, lean_object* v_b_63_){
_start:
{
lean_object* v_size_64_; lean_object* v_buckets_65_; lean_object* v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; uint64_t v___x_69_; uint64_t v_fold_70_; uint64_t v___x_71_; uint64_t v___x_72_; uint64_t v___x_73_; size_t v___x_74_; size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; size_t v___x_78_; lean_object* v_bkt_79_; uint8_t v___x_80_; 
v_size_64_ = lean_ctor_get(v_m_61_, 0);
v_buckets_65_ = lean_ctor_get(v_m_61_, 1);
v___x_66_ = lean_array_get_size(v_buckets_65_);
v___x_67_ = l_Lean_instHashableFVarId_hash(v_a_62_);
v___x_68_ = 32ULL;
v___x_69_ = lean_uint64_shift_right(v___x_67_, v___x_68_);
v_fold_70_ = lean_uint64_xor(v___x_67_, v___x_69_);
v___x_71_ = 16ULL;
v___x_72_ = lean_uint64_shift_right(v_fold_70_, v___x_71_);
v___x_73_ = lean_uint64_xor(v_fold_70_, v___x_72_);
v___x_74_ = lean_uint64_to_usize(v___x_73_);
v___x_75_ = lean_usize_of_nat(v___x_66_);
v___x_76_ = ((size_t)1ULL);
v___x_77_ = lean_usize_sub(v___x_75_, v___x_76_);
v___x_78_ = lean_usize_land(v___x_74_, v___x_77_);
v_bkt_79_ = lean_array_uget_borrowed(v_buckets_65_, v___x_78_);
v___x_80_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg(v_a_62_, v_bkt_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_101_; 
lean_inc_ref(v_buckets_65_);
lean_inc(v_size_64_);
v_isSharedCheck_101_ = !lean_is_exclusive(v_m_61_);
if (v_isSharedCheck_101_ == 0)
{
lean_object* v_unused_102_; lean_object* v_unused_103_; 
v_unused_102_ = lean_ctor_get(v_m_61_, 1);
lean_dec(v_unused_102_);
v_unused_103_ = lean_ctor_get(v_m_61_, 0);
lean_dec(v_unused_103_);
v___x_82_ = v_m_61_;
v_isShared_83_ = v_isSharedCheck_101_;
goto v_resetjp_81_;
}
else
{
lean_dec(v_m_61_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_101_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; lean_object* v_size_x27_85_; lean_object* v___x_86_; lean_object* v_buckets_x27_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_84_ = lean_unsigned_to_nat(1u);
v_size_x27_85_ = lean_nat_add(v_size_64_, v___x_84_);
lean_dec(v_size_64_);
lean_inc(v_bkt_79_);
v___x_86_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_86_, 0, v_a_62_);
lean_ctor_set(v___x_86_, 1, v_b_63_);
lean_ctor_set(v___x_86_, 2, v_bkt_79_);
v_buckets_x27_87_ = lean_array_uset(v_buckets_65_, v___x_78_, v___x_86_);
v___x_88_ = lean_unsigned_to_nat(4u);
v___x_89_ = lean_nat_mul(v_size_x27_85_, v___x_88_);
v___x_90_ = lean_unsigned_to_nat(3u);
v___x_91_ = lean_nat_div(v___x_89_, v___x_90_);
lean_dec(v___x_89_);
v___x_92_ = lean_array_get_size(v_buckets_x27_87_);
v___x_93_ = lean_nat_dec_le(v___x_91_, v___x_92_);
lean_dec(v___x_91_);
if (v___x_93_ == 0)
{
lean_object* v_val_94_; lean_object* v___x_96_; 
v_val_94_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1___redArg(v_buckets_x27_87_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 1, v_val_94_);
lean_ctor_set(v___x_82_, 0, v_size_x27_85_);
v___x_96_ = v___x_82_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_size_x27_85_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_val_94_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
else
{
lean_object* v___x_99_; 
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 1, v_buckets_x27_87_);
lean_ctor_set(v___x_82_, 0, v_size_x27_85_);
v___x_99_ = v___x_82_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_size_x27_85_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_buckets_x27_87_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
else
{
lean_dec(v_b_63_);
lean_dec(v_a_62_);
return v_m_61_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_markVisited___redArg(lean_object* v_fvarId_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___x_107_; lean_object* v_visited_108_; lean_object* v_params_109_; lean_object* v_decls_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_121_; 
v___x_107_ = lean_st_ref_take(v_a_105_);
v_visited_108_ = lean_ctor_get(v___x_107_, 0);
v_params_109_ = lean_ctor_get(v___x_107_, 1);
v_decls_110_ = lean_ctor_get(v___x_107_, 2);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_121_ == 0)
{
v___x_112_ = v___x_107_;
v_isShared_113_ = v_isSharedCheck_121_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_decls_110_);
lean_inc(v_params_109_);
lean_inc(v_visited_108_);
lean_dec(v___x_107_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_121_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_117_; 
v___x_114_ = lean_box(0);
v___x_115_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0___redArg(v_visited_108_, v_fvarId_104_, v___x_114_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v___x_115_);
v___x_117_ = v___x_112_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_params_109_);
lean_ctor_set(v_reuseFailAlloc_120_, 2, v_decls_110_);
v___x_117_ = v_reuseFailAlloc_120_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_st_ref_put(v_a_105_, v___x_117_);
v___x_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_114_);
return v___x_119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_markVisited___redArg___boxed(lean_object* v_fvarId_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Compiler_LCNF_Closure_markVisited___redArg(v_fvarId_122_, v_a_123_);
lean_dec(v_a_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_markVisited(lean_object* v_fvarId_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Compiler_LCNF_Closure_markVisited___redArg(v_fvarId_126_, v_a_128_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_markVisited___boxed(lean_object* v_fvarId_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Compiler_LCNF_Closure_markVisited(v_fvarId_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0(lean_object* v_00_u03b2_144_, lean_object* v_m_145_, lean_object* v_a_146_, lean_object* v_b_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0___redArg(v_m_145_, v_a_146_, v_b_147_);
return v___x_148_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0(lean_object* v_00_u03b2_149_, lean_object* v_a_150_, lean_object* v_x_151_){
_start:
{
uint8_t v___x_152_; 
v___x_152_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg(v_a_150_, v_x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___boxed(lean_object* v_00_u03b2_153_, lean_object* v_a_154_, lean_object* v_x_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0(v_00_u03b2_153_, v_a_154_, v_x_155_);
lean_dec(v_x_155_);
lean_dec(v_a_154_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1(lean_object* v_00_u03b2_158_, lean_object* v_data_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1___redArg(v_data_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_161_, lean_object* v_i_162_, lean_object* v_source_163_, lean_object* v_target_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2___redArg(v_i_162_, v_source_163_, v_target_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_166_, lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__1_spec__2_spec__3___redArg(v_x_167_, v_x_168_);
return v___x_169_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0(void){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_instMonadEIO___redArg();
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5(lean_object* v_msg_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v_toApplicative_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_248_; 
v___x_183_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__0);
v___x_184_ = l_StateRefT_x27_instMonad___redArg(v___x_183_);
v_toApplicative_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_248_ == 0)
{
lean_object* v_unused_249_; 
v_unused_249_ = lean_ctor_get(v___x_184_, 1);
lean_dec(v_unused_249_);
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_248_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_toApplicative_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_248_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v_toFunctor_189_; lean_object* v_toSeq_190_; lean_object* v_toSeqLeft_191_; lean_object* v_toSeqRight_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_246_; 
v_toFunctor_189_ = lean_ctor_get(v_toApplicative_185_, 0);
v_toSeq_190_ = lean_ctor_get(v_toApplicative_185_, 2);
v_toSeqLeft_191_ = lean_ctor_get(v_toApplicative_185_, 3);
v_toSeqRight_192_ = lean_ctor_get(v_toApplicative_185_, 4);
v_isSharedCheck_246_ = !lean_is_exclusive(v_toApplicative_185_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; 
v_unused_247_ = lean_ctor_get(v_toApplicative_185_, 1);
lean_dec(v_unused_247_);
v___x_194_ = v_toApplicative_185_;
v_isShared_195_ = v_isSharedCheck_246_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_toSeqRight_192_);
lean_inc(v_toSeqLeft_191_);
lean_inc(v_toSeq_190_);
lean_inc(v_toFunctor_189_);
lean_dec(v_toApplicative_185_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_246_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___x_200_; lean_object* v___f_201_; lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___x_205_; 
v___f_196_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__1));
v___f_197_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__2));
lean_inc_ref(v_toFunctor_189_);
v___f_198_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_198_, 0, v_toFunctor_189_);
v___f_199_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_199_, 0, v_toFunctor_189_);
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v___f_198_);
lean_ctor_set(v___x_200_, 1, v___f_199_);
v___f_201_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_201_, 0, v_toSeqRight_192_);
v___f_202_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_202_, 0, v_toSeqLeft_191_);
v___f_203_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_203_, 0, v_toSeq_190_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 4, v___f_201_);
lean_ctor_set(v___x_194_, 3, v___f_202_);
lean_ctor_set(v___x_194_, 2, v___f_203_);
lean_ctor_set(v___x_194_, 1, v___f_196_);
lean_ctor_set(v___x_194_, 0, v___x_200_);
v___x_205_ = v___x_194_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v___f_196_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v___f_203_);
lean_ctor_set(v_reuseFailAlloc_245_, 3, v___f_202_);
lean_ctor_set(v_reuseFailAlloc_245_, 4, v___f_201_);
v___x_205_ = v_reuseFailAlloc_245_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_207_; 
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 1, v___f_197_);
lean_ctor_set(v___x_187_, 0, v___x_205_);
v___x_207_ = v___x_187_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_205_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v___f_197_);
v___x_207_ = v_reuseFailAlloc_244_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_208_; lean_object* v_toApplicative_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_242_; 
v___x_208_ = l_StateRefT_x27_instMonad___redArg(v___x_207_);
v_toApplicative_209_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_242_ == 0)
{
lean_object* v_unused_243_; 
v_unused_243_ = lean_ctor_get(v___x_208_, 1);
lean_dec(v_unused_243_);
v___x_211_ = v___x_208_;
v_isShared_212_ = v_isSharedCheck_242_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_toApplicative_209_);
lean_dec(v___x_208_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_242_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v_toFunctor_213_; lean_object* v_toSeq_214_; lean_object* v_toSeqLeft_215_; lean_object* v_toSeqRight_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_240_; 
v_toFunctor_213_ = lean_ctor_get(v_toApplicative_209_, 0);
v_toSeq_214_ = lean_ctor_get(v_toApplicative_209_, 2);
v_toSeqLeft_215_ = lean_ctor_get(v_toApplicative_209_, 3);
v_toSeqRight_216_ = lean_ctor_get(v_toApplicative_209_, 4);
v_isSharedCheck_240_ = !lean_is_exclusive(v_toApplicative_209_);
if (v_isSharedCheck_240_ == 0)
{
lean_object* v_unused_241_; 
v_unused_241_ = lean_ctor_get(v_toApplicative_209_, 1);
lean_dec(v_unused_241_);
v___x_218_ = v_toApplicative_209_;
v_isShared_219_ = v_isSharedCheck_240_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_toSeqRight_216_);
lean_inc(v_toSeqLeft_215_);
lean_inc(v_toSeq_214_);
lean_inc(v_toFunctor_213_);
lean_dec(v_toApplicative_209_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_240_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___f_220_; lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___f_223_; lean_object* v___x_224_; lean_object* v___f_225_; lean_object* v___f_226_; lean_object* v___f_227_; lean_object* v___x_229_; 
v___f_220_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__3));
v___f_221_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___closed__4));
lean_inc_ref(v_toFunctor_213_);
v___f_222_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_222_, 0, v_toFunctor_213_);
v___f_223_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_223_, 0, v_toFunctor_213_);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v___f_222_);
lean_ctor_set(v___x_224_, 1, v___f_223_);
v___f_225_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_225_, 0, v_toSeqRight_216_);
v___f_226_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_226_, 0, v_toSeqLeft_215_);
v___f_227_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_227_, 0, v_toSeq_214_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 4, v___f_225_);
lean_ctor_set(v___x_218_, 3, v___f_226_);
lean_ctor_set(v___x_218_, 2, v___f_227_);
lean_ctor_set(v___x_218_, 1, v___f_220_);
lean_ctor_set(v___x_218_, 0, v___x_224_);
v___x_229_ = v___x_218_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v___f_220_);
lean_ctor_set(v_reuseFailAlloc_239_, 2, v___f_227_);
lean_ctor_set(v_reuseFailAlloc_239_, 3, v___f_226_);
lean_ctor_set(v_reuseFailAlloc_239_, 4, v___f_225_);
v___x_229_ = v_reuseFailAlloc_239_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_231_; 
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 1, v___f_221_);
lean_ctor_set(v___x_211_, 0, v___x_229_);
v___x_231_ = v___x_211_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v___f_221_);
v___x_231_ = v_reuseFailAlloc_238_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___f_235_; lean_object* v___x_19459__overap_236_; lean_object* v___x_237_; 
v___x_232_ = l_StateRefT_x27_instMonad___redArg(v___x_231_);
v___x_233_ = lean_box(0);
v___x_234_ = l_instInhabitedOfMonad___redArg(v___x_232_, v___x_233_);
v___f_235_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_235_, 0, v___x_234_);
v___x_19459__overap_236_ = lean_panic_fn_borrowed(v___f_235_, v_msg_175_);
lean_dec_ref(v___f_235_);
lean_inc(v___y_181_);
lean_inc_ref(v___y_180_);
lean_inc(v___y_179_);
lean_inc_ref(v___y_178_);
lean_inc(v___y_177_);
lean_inc_ref(v___y_176_);
v___x_237_ = lean_apply_7(v___x_19459__overap_236_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, lean_box(0));
return v___x_237_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5___boxed(lean_object* v_msg_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5(v_msg_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
return v_res_258_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(lean_object* v_a_259_, lean_object* v_x_260_){
_start:
{
if (lean_obj_tag(v_x_260_) == 0)
{
uint8_t v___x_261_; 
v___x_261_ = 0;
return v___x_261_;
}
else
{
lean_object* v_key_262_; lean_object* v_tail_263_; uint8_t v___x_264_; 
v_key_262_ = lean_ctor_get(v_x_260_, 0);
v_tail_263_ = lean_ctor_get(v_x_260_, 2);
v___x_264_ = lean_expr_eqv(v_key_262_, v_a_259_);
if (v___x_264_ == 0)
{
v_x_260_ = v_tail_263_;
goto _start;
}
else
{
return v___x_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg___boxed(lean_object* v_a_266_, lean_object* v_x_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(v_a_266_, v_x_267_);
lean_dec(v_x_267_);
lean_dec_ref(v_a_266_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg(lean_object* v_m_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_buckets_272_; lean_object* v___x_273_; uint64_t v___x_274_; uint64_t v___x_275_; uint64_t v___x_276_; uint64_t v_fold_277_; uint64_t v___x_278_; uint64_t v___x_279_; uint64_t v___x_280_; size_t v___x_281_; size_t v___x_282_; size_t v___x_283_; size_t v___x_284_; size_t v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v_buckets_272_ = lean_ctor_get(v_m_270_, 1);
v___x_273_ = lean_array_get_size(v_buckets_272_);
v___x_274_ = l_Lean_Expr_hash(v_a_271_);
v___x_275_ = 32ULL;
v___x_276_ = lean_uint64_shift_right(v___x_274_, v___x_275_);
v_fold_277_ = lean_uint64_xor(v___x_274_, v___x_276_);
v___x_278_ = 16ULL;
v___x_279_ = lean_uint64_shift_right(v_fold_277_, v___x_278_);
v___x_280_ = lean_uint64_xor(v_fold_277_, v___x_279_);
v___x_281_ = lean_uint64_to_usize(v___x_280_);
v___x_282_ = lean_usize_of_nat(v___x_273_);
v___x_283_ = ((size_t)1ULL);
v___x_284_ = lean_usize_sub(v___x_282_, v___x_283_);
v___x_285_ = lean_usize_land(v___x_281_, v___x_284_);
v___x_286_ = lean_array_uget_borrowed(v_buckets_272_, v___x_285_);
v___x_287_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(v_a_271_, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg___boxed(lean_object* v_m_288_, lean_object* v_a_289_){
_start:
{
uint8_t v_res_290_; lean_object* v_r_291_; 
v_res_290_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg(v_m_288_, v_a_289_);
lean_dec_ref(v_a_289_);
lean_dec_ref(v_m_288_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18_spec__19___redArg(lean_object* v_x_292_, lean_object* v_x_293_){
_start:
{
if (lean_obj_tag(v_x_293_) == 0)
{
return v_x_292_;
}
else
{
lean_object* v_key_294_; lean_object* v_value_295_; lean_object* v_tail_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_319_; 
v_key_294_ = lean_ctor_get(v_x_293_, 0);
v_value_295_ = lean_ctor_get(v_x_293_, 1);
v_tail_296_ = lean_ctor_get(v_x_293_, 2);
v_isSharedCheck_319_ = !lean_is_exclusive(v_x_293_);
if (v_isSharedCheck_319_ == 0)
{
v___x_298_ = v_x_293_;
v_isShared_299_ = v_isSharedCheck_319_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_tail_296_);
lean_inc(v_value_295_);
lean_inc(v_key_294_);
lean_dec(v_x_293_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_319_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; uint64_t v___x_301_; uint64_t v___x_302_; uint64_t v___x_303_; uint64_t v_fold_304_; uint64_t v___x_305_; uint64_t v___x_306_; uint64_t v___x_307_; size_t v___x_308_; size_t v___x_309_; size_t v___x_310_; size_t v___x_311_; size_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_300_ = lean_array_get_size(v_x_292_);
v___x_301_ = l_Lean_Expr_hash(v_key_294_);
v___x_302_ = 32ULL;
v___x_303_ = lean_uint64_shift_right(v___x_301_, v___x_302_);
v_fold_304_ = lean_uint64_xor(v___x_301_, v___x_303_);
v___x_305_ = 16ULL;
v___x_306_ = lean_uint64_shift_right(v_fold_304_, v___x_305_);
v___x_307_ = lean_uint64_xor(v_fold_304_, v___x_306_);
v___x_308_ = lean_uint64_to_usize(v___x_307_);
v___x_309_ = lean_usize_of_nat(v___x_300_);
v___x_310_ = ((size_t)1ULL);
v___x_311_ = lean_usize_sub(v___x_309_, v___x_310_);
v___x_312_ = lean_usize_land(v___x_308_, v___x_311_);
v___x_313_ = lean_array_uget_borrowed(v_x_292_, v___x_312_);
lean_inc(v___x_313_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 2, v___x_313_);
v___x_315_ = v___x_298_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_key_294_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_value_295_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v___x_313_);
v___x_315_ = v_reuseFailAlloc_318_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_316_; 
v___x_316_ = lean_array_uset(v_x_292_, v___x_312_, v___x_315_);
v_x_292_ = v___x_316_;
v_x_293_ = v_tail_296_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18___redArg(lean_object* v_i_320_, lean_object* v_source_321_, lean_object* v_target_322_){
_start:
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = lean_array_get_size(v_source_321_);
v___x_324_ = lean_nat_dec_lt(v_i_320_, v___x_323_);
if (v___x_324_ == 0)
{
lean_dec_ref(v_source_321_);
lean_dec(v_i_320_);
return v_target_322_;
}
else
{
lean_object* v_es_325_; lean_object* v___x_326_; lean_object* v_source_327_; lean_object* v_target_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_es_325_ = lean_array_fget(v_source_321_, v_i_320_);
v___x_326_ = lean_box(0);
v_source_327_ = lean_array_fset(v_source_321_, v_i_320_, v___x_326_);
v_target_328_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18_spec__19___redArg(v_target_322_, v_es_325_);
v___x_329_ = lean_unsigned_to_nat(1u);
v___x_330_ = lean_nat_add(v_i_320_, v___x_329_);
lean_dec(v_i_320_);
v_i_320_ = v___x_330_;
v_source_321_ = v_source_327_;
v_target_322_ = v_target_328_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17___redArg(lean_object* v_data_332_){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v_nbuckets_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_333_ = lean_array_get_size(v_data_332_);
v___x_334_ = lean_unsigned_to_nat(2u);
v_nbuckets_335_ = lean_nat_mul(v___x_333_, v___x_334_);
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = lean_box(0);
v___x_338_ = lean_mk_array(v_nbuckets_335_, v___x_337_);
v___x_339_ = lean_array_propagate_mark(v_data_332_, v___x_338_);
v___x_340_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18___redArg(v___x_336_, v_data_332_, v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15___redArg(lean_object* v_m_341_, lean_object* v_a_342_, lean_object* v_b_343_){
_start:
{
lean_object* v_size_344_; lean_object* v_buckets_345_; lean_object* v___x_346_; uint64_t v___x_347_; uint64_t v___x_348_; uint64_t v___x_349_; uint64_t v_fold_350_; uint64_t v___x_351_; uint64_t v___x_352_; uint64_t v___x_353_; size_t v___x_354_; size_t v___x_355_; size_t v___x_356_; size_t v___x_357_; size_t v___x_358_; lean_object* v_bkt_359_; uint8_t v___x_360_; 
v_size_344_ = lean_ctor_get(v_m_341_, 0);
v_buckets_345_ = lean_ctor_get(v_m_341_, 1);
v___x_346_ = lean_array_get_size(v_buckets_345_);
v___x_347_ = l_Lean_Expr_hash(v_a_342_);
v___x_348_ = 32ULL;
v___x_349_ = lean_uint64_shift_right(v___x_347_, v___x_348_);
v_fold_350_ = lean_uint64_xor(v___x_347_, v___x_349_);
v___x_351_ = 16ULL;
v___x_352_ = lean_uint64_shift_right(v_fold_350_, v___x_351_);
v___x_353_ = lean_uint64_xor(v_fold_350_, v___x_352_);
v___x_354_ = lean_uint64_to_usize(v___x_353_);
v___x_355_ = lean_usize_of_nat(v___x_346_);
v___x_356_ = ((size_t)1ULL);
v___x_357_ = lean_usize_sub(v___x_355_, v___x_356_);
v___x_358_ = lean_usize_land(v___x_354_, v___x_357_);
v_bkt_359_ = lean_array_uget_borrowed(v_buckets_345_, v___x_358_);
v___x_360_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(v_a_342_, v_bkt_359_);
if (v___x_360_ == 0)
{
lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_381_; 
lean_inc_ref(v_buckets_345_);
lean_inc(v_size_344_);
v_isSharedCheck_381_ = !lean_is_exclusive(v_m_341_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; lean_object* v_unused_383_; 
v_unused_382_ = lean_ctor_get(v_m_341_, 1);
lean_dec(v_unused_382_);
v_unused_383_ = lean_ctor_get(v_m_341_, 0);
lean_dec(v_unused_383_);
v___x_362_ = v_m_341_;
v_isShared_363_ = v_isSharedCheck_381_;
goto v_resetjp_361_;
}
else
{
lean_dec(v_m_341_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_381_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v_size_x27_365_; lean_object* v___x_366_; lean_object* v_buckets_x27_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_364_ = lean_unsigned_to_nat(1u);
v_size_x27_365_ = lean_nat_add(v_size_344_, v___x_364_);
lean_dec(v_size_344_);
lean_inc(v_bkt_359_);
v___x_366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_366_, 0, v_a_342_);
lean_ctor_set(v___x_366_, 1, v_b_343_);
lean_ctor_set(v___x_366_, 2, v_bkt_359_);
v_buckets_x27_367_ = lean_array_uset(v_buckets_345_, v___x_358_, v___x_366_);
v___x_368_ = lean_unsigned_to_nat(4u);
v___x_369_ = lean_nat_mul(v_size_x27_365_, v___x_368_);
v___x_370_ = lean_unsigned_to_nat(3u);
v___x_371_ = lean_nat_div(v___x_369_, v___x_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_array_get_size(v_buckets_x27_367_);
v___x_373_ = lean_nat_dec_le(v___x_371_, v___x_372_);
lean_dec(v___x_371_);
if (v___x_373_ == 0)
{
lean_object* v_val_374_; lean_object* v___x_376_; 
v_val_374_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17___redArg(v_buckets_x27_367_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 1, v_val_374_);
lean_ctor_set(v___x_362_, 0, v_size_x27_365_);
v___x_376_ = v___x_362_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_size_x27_365_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_val_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
else
{
lean_object* v___x_379_; 
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 1, v_buckets_x27_367_);
lean_ctor_set(v___x_362_, 0, v_size_x27_365_);
v___x_379_ = v___x_362_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_size_x27_365_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_buckets_x27_367_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
else
{
lean_dec(v_b_343_);
lean_dec_ref(v_a_342_);
return v_m_341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg(lean_object* v_e_384_, lean_object* v_a_385_){
_start:
{
lean_object* v___x_387_; lean_object* v_checked_388_; uint8_t v___x_389_; 
v___x_387_ = lean_st_ref_get(v_a_385_);
v_checked_388_ = lean_ctor_get(v___x_387_, 1);
lean_inc_ref(v_checked_388_);
lean_dec(v___x_387_);
v___x_389_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg(v_checked_388_, v_e_384_);
lean_dec_ref(v_checked_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; lean_object* v_visited_391_; lean_object* v_checked_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_404_; 
v___x_390_ = lean_st_ref_take(v_a_385_);
v_visited_391_ = lean_ctor_get(v___x_390_, 0);
v_checked_392_ = lean_ctor_get(v___x_390_, 1);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_404_ == 0)
{
v___x_394_ = v___x_390_;
v_isShared_395_ = v_isSharedCheck_404_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_checked_392_);
lean_inc(v_visited_391_);
lean_dec(v___x_390_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_404_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_396_ = lean_box(0);
v___x_397_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15___redArg(v_checked_392_, v_e_384_, v___x_396_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 1, v___x_397_);
v___x_399_ = v___x_394_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_visited_391_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v___x_397_);
v___x_399_ = v_reuseFailAlloc_403_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_400_ = lean_st_ref_put(v_a_385_, v___x_399_);
v___x_401_ = lean_box(v___x_389_);
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
return v___x_402_;
}
}
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec_ref(v_e_384_);
v___x_405_ = lean_box(v___x_389_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg___boxed(lean_object* v_e_407_, lean_object* v_a_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg(v_e_407_, v_a_408_);
lean_dec(v_a_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg(lean_object* v_e_411_, lean_object* v_a_412_){
_start:
{
lean_object* v___x_414_; lean_object* v_visited_415_; size_t v___x_416_; size_t v___x_417_; size_t v___x_418_; lean_object* v___x_419_; size_t v___x_420_; uint8_t v___x_421_; 
v___x_414_ = lean_st_ref_get(v_a_412_);
v_visited_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc_ref(v_visited_415_);
lean_dec(v___x_414_);
v___x_416_ = lean_ptr_addr(v_e_411_);
v___x_417_ = ((size_t)8191ULL);
v___x_418_ = lean_usize_mod(v___x_416_, v___x_417_);
v___x_419_ = lean_array_uget(v_visited_415_, v___x_418_);
lean_dec_ref(v_visited_415_);
v___x_420_ = lean_ptr_addr(v___x_419_);
lean_dec(v___x_419_);
v___x_421_ = lean_usize_dec_eq(v___x_420_, v___x_416_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v_visited_423_; lean_object* v_checked_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_435_; 
v___x_422_ = lean_st_ref_take(v_a_412_);
v_visited_423_ = lean_ctor_get(v___x_422_, 0);
v_checked_424_ = lean_ctor_get(v___x_422_, 1);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_435_ == 0)
{
v___x_426_ = v___x_422_;
v_isShared_427_ = v_isSharedCheck_435_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_checked_424_);
lean_inc(v_visited_423_);
lean_dec(v___x_422_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_435_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_428_ = lean_array_uset(v_visited_423_, v___x_418_, v_e_411_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_428_);
v___x_430_ = v___x_426_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_checked_424_);
v___x_430_ = v_reuseFailAlloc_434_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = lean_st_ref_put(v_a_412_, v___x_430_);
v___x_432_ = lean_box(v___x_421_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
}
else
{
lean_object* v___x_436_; lean_object* v___x_437_; 
lean_dec_ref(v_e_411_);
v___x_436_ = lean_box(v___x_421_);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg___boxed(lean_object* v_e_438_, lean_object* v_a_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg(v_e_438_, v_a_439_);
lean_dec(v_a_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(lean_object* v_p_442_, lean_object* v_f_443_, uint8_t v_stopWhenVisited_444_, lean_object* v_e_445_, lean_object* v_a_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v_d_461_; lean_object* v_b_462_; lean_object* v___y_463_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___x_494_; 
lean_inc_ref(v_e_445_);
v___x_494_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg(v_e_445_, v_a_446_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_527_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_527_ == 0)
{
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_527_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_527_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
uint8_t v___x_499_; 
v___x_499_ = lean_unbox(v_a_495_);
lean_dec(v_a_495_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; uint8_t v___x_501_; 
lean_del_object(v___x_497_);
lean_inc_ref(v_p_442_);
lean_inc_ref(v_e_445_);
v___x_500_ = lean_apply_1(v_p_442_, v_e_445_);
v___x_501_ = lean_unbox(v___x_500_);
if (v___x_501_ == 0)
{
v___y_467_ = v_a_446_;
v___y_468_ = v___y_447_;
v___y_469_ = v___y_448_;
v___y_470_ = v___y_449_;
v___y_471_ = v___y_450_;
v___y_472_ = v___y_451_;
v___y_473_ = v___y_452_;
goto v___jp_466_;
}
else
{
lean_object* v___x_502_; 
lean_inc_ref(v_e_445_);
v___x_502_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg(v_e_445_, v_a_446_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; uint8_t v___x_504_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref_known(v___x_502_, 1);
v___x_504_ = lean_unbox(v_a_503_);
lean_dec(v_a_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; 
lean_inc_ref(v_f_443_);
lean_inc(v___y_452_);
lean_inc_ref(v___y_451_);
lean_inc(v___y_450_);
lean_inc_ref(v___y_449_);
lean_inc(v___y_448_);
lean_inc_ref(v___y_447_);
lean_inc_ref(v_e_445_);
v___x_505_ = lean_apply_8(v_f_443_, v_e_445_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, lean_box(0));
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_513_; 
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_513_ == 0)
{
lean_object* v_unused_514_; 
v_unused_514_ = lean_ctor_get(v___x_505_, 0);
lean_dec(v_unused_514_);
v___x_507_ = v___x_505_;
v_isShared_508_ = v_isSharedCheck_513_;
goto v_resetjp_506_;
}
else
{
lean_dec(v___x_505_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_513_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
if (v_stopWhenVisited_444_ == 0)
{
lean_del_object(v___x_507_);
v___y_467_ = v_a_446_;
v___y_468_ = v___y_447_;
v___y_469_ = v___y_448_;
v___y_470_ = v___y_449_;
v___y_471_ = v___y_450_;
v___y_472_ = v___y_451_;
v___y_473_ = v___y_452_;
goto v___jp_466_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_511_; 
lean_dec_ref(v_e_445_);
lean_dec_ref(v_f_443_);
lean_dec_ref(v_p_442_);
v___x_509_ = lean_box(0);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_509_);
v___x_511_ = v___x_507_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
else
{
lean_dec_ref(v_e_445_);
lean_dec_ref(v_f_443_);
lean_dec_ref(v_p_442_);
return v___x_505_;
}
}
else
{
v___y_467_ = v_a_446_;
v___y_468_ = v___y_447_;
v___y_469_ = v___y_448_;
v___y_470_ = v___y_449_;
v___y_471_ = v___y_450_;
v___y_472_ = v___y_451_;
v___y_473_ = v___y_452_;
goto v___jp_466_;
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
lean_dec_ref(v_e_445_);
lean_dec_ref(v_f_443_);
lean_dec_ref(v_p_442_);
v_a_515_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_502_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_502_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
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
}
else
{
lean_object* v___x_523_; lean_object* v___x_525_; 
lean_dec_ref(v_e_445_);
lean_dec_ref(v_f_443_);
lean_dec_ref(v_p_442_);
v___x_523_ = lean_box(0);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_523_);
v___x_525_ = v___x_497_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec_ref(v_e_445_);
lean_dec_ref(v_f_443_);
lean_dec_ref(v_p_442_);
v_a_528_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_494_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_494_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
v___jp_454_:
{
lean_object* v___x_464_; 
lean_inc_ref(v_f_443_);
lean_inc_ref(v_p_442_);
v___x_464_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_442_, v_f_443_, v_stopWhenVisited_444_, v_d_461_, v___y_463_, v___y_459_, v___y_460_, v___y_456_, v___y_458_, v___y_457_, v___y_455_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_dec_ref_known(v___x_464_, 1);
v_e_445_ = v_b_462_;
v_a_446_ = v___y_463_;
v___y_447_ = v___y_459_;
v___y_448_ = v___y_460_;
v___y_449_ = v___y_456_;
v___y_450_ = v___y_458_;
v___y_451_ = v___y_457_;
v___y_452_ = v___y_455_;
goto _start;
}
else
{
lean_dec_ref(v_b_462_);
lean_dec_ref(v_f_443_);
lean_dec_ref(v_p_442_);
return v___x_464_;
}
}
v___jp_466_:
{
switch(lean_obj_tag(v_e_445_))
{
case 7:
{
lean_object* v_binderType_474_; lean_object* v_body_475_; 
v_binderType_474_ = lean_ctor_get(v_e_445_, 1);
lean_inc_ref(v_binderType_474_);
v_body_475_ = lean_ctor_get(v_e_445_, 2);
lean_inc_ref(v_body_475_);
lean_dec_ref_known(v_e_445_, 3);
v___y_455_ = v___y_473_;
v___y_456_ = v___y_470_;
v___y_457_ = v___y_472_;
v___y_458_ = v___y_471_;
v___y_459_ = v___y_468_;
v___y_460_ = v___y_469_;
v_d_461_ = v_binderType_474_;
v_b_462_ = v_body_475_;
v___y_463_ = v___y_467_;
goto v___jp_454_;
}
case 6:
{
lean_object* v_binderType_476_; lean_object* v_body_477_; 
v_binderType_476_ = lean_ctor_get(v_e_445_, 1);
lean_inc_ref(v_binderType_476_);
v_body_477_ = lean_ctor_get(v_e_445_, 2);
lean_inc_ref(v_body_477_);
lean_dec_ref_known(v_e_445_, 3);
v___y_455_ = v___y_473_;
v___y_456_ = v___y_470_;
v___y_457_ = v___y_472_;
v___y_458_ = v___y_471_;
v___y_459_ = v___y_468_;
v___y_460_ = v___y_469_;
v_d_461_ = v_binderType_476_;
v_b_462_ = v_body_477_;
v___y_463_ = v___y_467_;
goto v___jp_454_;
}
case 8:
{
lean_object* v_type_478_; lean_object* v_value_479_; lean_object* v_body_480_; lean_object* v___x_481_; 
v_type_478_ = lean_ctor_get(v_e_445_, 1);
lean_inc_ref(v_type_478_);
v_value_479_ = lean_ctor_get(v_e_445_, 2);
lean_inc_ref(v_value_479_);
v_body_480_ = lean_ctor_get(v_e_445_, 3);
lean_inc_ref(v_body_480_);
lean_dec_ref_known(v_e_445_, 4);
lean_inc_ref(v_f_443_);
lean_inc_ref(v_p_442_);
v___x_481_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_442_, v_f_443_, v_stopWhenVisited_444_, v_type_478_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v___x_482_; 
lean_dec_ref_known(v___x_481_, 1);
lean_inc_ref(v_f_443_);
lean_inc_ref(v_p_442_);
v___x_482_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_442_, v_f_443_, v_stopWhenVisited_444_, v_value_479_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_dec_ref_known(v___x_482_, 1);
v_e_445_ = v_body_480_;
v_a_446_ = v___y_467_;
v___y_447_ = v___y_468_;
v___y_448_ = v___y_469_;
v___y_449_ = v___y_470_;
v___y_450_ = v___y_471_;
v___y_451_ = v___y_472_;
v___y_452_ = v___y_473_;
goto _start;
}
else
{
lean_dec_ref(v_body_480_);
lean_dec_ref(v_f_443_);
lean_dec_ref(v_p_442_);
return v___x_482_;
}
}
else
{
lean_dec_ref(v_body_480_);
lean_dec_ref(v_value_479_);
lean_dec_ref(v_f_443_);
lean_dec_ref(v_p_442_);
return v___x_481_;
}
}
case 5:
{
lean_object* v_fn_484_; lean_object* v_arg_485_; lean_object* v___x_486_; 
v_fn_484_ = lean_ctor_get(v_e_445_, 0);
lean_inc_ref(v_fn_484_);
v_arg_485_ = lean_ctor_get(v_e_445_, 1);
lean_inc_ref(v_arg_485_);
lean_dec_ref_known(v_e_445_, 2);
lean_inc_ref(v_f_443_);
lean_inc_ref(v_p_442_);
v___x_486_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_442_, v_f_443_, v_stopWhenVisited_444_, v_fn_484_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_dec_ref_known(v___x_486_, 1);
v_e_445_ = v_arg_485_;
v_a_446_ = v___y_467_;
v___y_447_ = v___y_468_;
v___y_448_ = v___y_469_;
v___y_449_ = v___y_470_;
v___y_450_ = v___y_471_;
v___y_451_ = v___y_472_;
v___y_452_ = v___y_473_;
goto _start;
}
else
{
lean_dec_ref(v_arg_485_);
lean_dec_ref(v_f_443_);
lean_dec_ref(v_p_442_);
return v___x_486_;
}
}
case 10:
{
lean_object* v_expr_488_; 
v_expr_488_ = lean_ctor_get(v_e_445_, 1);
lean_inc_ref(v_expr_488_);
lean_dec_ref_known(v_e_445_, 2);
v_e_445_ = v_expr_488_;
v_a_446_ = v___y_467_;
v___y_447_ = v___y_468_;
v___y_448_ = v___y_469_;
v___y_449_ = v___y_470_;
v___y_450_ = v___y_471_;
v___y_451_ = v___y_472_;
v___y_452_ = v___y_473_;
goto _start;
}
case 11:
{
lean_object* v_struct_490_; 
v_struct_490_ = lean_ctor_get(v_e_445_, 2);
lean_inc_ref(v_struct_490_);
lean_dec_ref_known(v_e_445_, 3);
v_e_445_ = v_struct_490_;
v_a_446_ = v___y_467_;
v___y_447_ = v___y_468_;
v___y_448_ = v___y_469_;
v___y_449_ = v___y_470_;
v___y_450_ = v___y_471_;
v___y_451_ = v___y_472_;
v___y_452_ = v___y_473_;
goto _start;
}
default: 
{
lean_object* v___x_492_; lean_object* v___x_493_; 
lean_dec_ref(v_e_445_);
lean_dec_ref(v_f_443_);
lean_dec_ref(v_p_442_);
v___x_492_ = lean_box(0);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4___boxed(lean_object* v_p_536_, lean_object* v_f_537_, lean_object* v_stopWhenVisited_538_, lean_object* v_e_539_, lean_object* v_a_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
uint8_t v_stopWhenVisited_boxed_548_; lean_object* v_res_549_; 
v_stopWhenVisited_boxed_548_ = lean_unbox(v_stopWhenVisited_538_);
v_res_549_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_536_, v_f_537_, v_stopWhenVisited_boxed_548_, v_e_539_, v_a_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v_a_540_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2(lean_object* v_p_550_, lean_object* v_f_551_, lean_object* v_e_552_, uint8_t v_stopWhenVisited_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = l_Lean_ForEachExprWhere_initCache;
v___x_562_ = lean_st_mk_ref(v___x_561_);
v___x_563_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_550_, v_f_551_, v_stopWhenVisited_553_, v_e_552_, v___x_562_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_572_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_572_ == 0)
{
v___x_566_ = v___x_563_;
v_isShared_567_ = v_isSharedCheck_572_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_563_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_572_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = lean_st_ref_get(v___x_562_);
lean_dec(v___x_562_);
lean_dec(v___x_568_);
if (v_isShared_567_ == 0)
{
v___x_570_ = v___x_566_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_564_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
else
{
lean_dec(v___x_562_);
return v___x_563_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2___boxed(lean_object* v_p_573_, lean_object* v_f_574_, lean_object* v_e_575_, lean_object* v_stopWhenVisited_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
uint8_t v_stopWhenVisited_boxed_584_; lean_object* v_res_585_; 
v_stopWhenVisited_boxed_584_ = lean_unbox(v_stopWhenVisited_576_);
v_res_585_ = l_Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2(v_p_573_, v_f_574_, v_e_575_, v_stopWhenVisited_boxed_584_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
return v_res_585_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg(lean_object* v_m_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_buckets_588_; lean_object* v___x_589_; uint64_t v___x_590_; uint64_t v___x_591_; uint64_t v___x_592_; uint64_t v_fold_593_; uint64_t v___x_594_; uint64_t v___x_595_; uint64_t v___x_596_; size_t v___x_597_; size_t v___x_598_; size_t v___x_599_; size_t v___x_600_; size_t v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v_buckets_588_ = lean_ctor_get(v_m_586_, 1);
v___x_589_ = lean_array_get_size(v_buckets_588_);
v___x_590_ = l_Lean_instHashableFVarId_hash(v_a_587_);
v___x_591_ = 32ULL;
v___x_592_ = lean_uint64_shift_right(v___x_590_, v___x_591_);
v_fold_593_ = lean_uint64_xor(v___x_590_, v___x_592_);
v___x_594_ = 16ULL;
v___x_595_ = lean_uint64_shift_right(v_fold_593_, v___x_594_);
v___x_596_ = lean_uint64_xor(v_fold_593_, v___x_595_);
v___x_597_ = lean_uint64_to_usize(v___x_596_);
v___x_598_ = lean_usize_of_nat(v___x_589_);
v___x_599_ = ((size_t)1ULL);
v___x_600_ = lean_usize_sub(v___x_598_, v___x_599_);
v___x_601_ = lean_usize_land(v___x_597_, v___x_600_);
v___x_602_ = lean_array_uget_borrowed(v_buckets_588_, v___x_601_);
v___x_603_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Closure_markVisited_spec__0_spec__0___redArg(v_a_587_, v___x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg___boxed(lean_object* v_m_604_, lean_object* v_a_605_){
_start:
{
uint8_t v_res_606_; lean_object* v_r_607_; 
v_res_606_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg(v_m_604_, v_a_605_);
lean_dec(v_a_605_);
lean_dec_ref(v_m_604_);
v_r_607_ = lean_box(v_res_606_);
return v_r_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType___lam__0___boxed(lean_object* v_e_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Compiler_LCNF_Closure_collectType___lam__0(v_e_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec_ref(v_e_608_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType(lean_object* v_type_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
uint8_t v___x_626_; 
v___x_626_ = l_Lean_Expr_hasFVar(v_type_618_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; 
lean_dec_ref(v_type_618_);
v___x_627_ = lean_box(0);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
else
{
lean_object* v___f_629_; lean_object* v___x_630_; uint8_t v___x_631_; lean_object* v___x_632_; 
v___f_629_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Closure_collectType___lam__0___boxed), 8, 0);
v___x_630_ = ((lean_object*)(l_Lean_Compiler_LCNF_Closure_collectType___closed__0));
v___x_631_ = 0;
v___x_632_ = l_Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2(v___x_630_, v___f_629_, v_type_618_, v___x_631_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_);
return v___x_632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0(lean_object* v_as_633_, size_t v_i_634_, size_t v_stop_635_, lean_object* v_b_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
uint8_t v___x_644_; 
v___x_644_ = lean_usize_dec_eq(v_i_634_, v_stop_635_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v_type_646_; lean_object* v___x_647_; 
v___x_645_ = lean_array_uget_borrowed(v_as_633_, v_i_634_);
v_type_646_ = lean_ctor_get(v___x_645_, 2);
lean_inc_ref(v_type_646_);
v___x_647_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_646_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; size_t v___x_649_; size_t v___x_650_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_647_, 1);
v___x_649_ = ((size_t)1ULL);
v___x_650_ = lean_usize_add(v_i_634_, v___x_649_);
v_i_634_ = v___x_650_;
v_b_636_ = v_a_648_;
goto _start;
}
else
{
return v___x_647_;
}
}
else
{
lean_object* v___x_652_; 
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v_b_636_);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectParams(lean_object* v_params_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_661_ = lean_unsigned_to_nat(0u);
v___x_662_ = lean_array_get_size(v_params_653_);
v___x_663_ = lean_box(0);
v___x_664_ = lean_nat_dec_lt(v___x_661_, v___x_662_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
return v___x_665_;
}
else
{
size_t v___x_666_; size_t v___x_667_; lean_object* v___x_668_; 
v___x_666_ = ((size_t)0ULL);
v___x_667_ = lean_usize_of_nat(v___x_662_);
v___x_668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0(v_params_653_, v___x_666_, v___x_667_, v___x_663_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
return v___x_668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectArg(lean_object* v_arg_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
switch(lean_obj_tag(v_arg_669_))
{
case 0:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_box(0);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
case 1:
{
lean_object* v_fvarId_679_; lean_object* v___x_680_; 
v_fvarId_679_ = lean_ctor_get(v_arg_669_, 0);
lean_inc(v_fvarId_679_);
lean_dec_ref_known(v_arg_669_, 1);
v___x_680_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v_fvarId_679_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
return v___x_680_;
}
default: 
{
lean_object* v_expr_681_; lean_object* v___x_682_; 
v_expr_681_ = lean_ctor_get(v_arg_669_, 0);
lean_inc_ref(v_expr_681_);
lean_dec_ref_known(v_arg_669_, 1);
v___x_682_ = l_Lean_Compiler_LCNF_Closure_collectType(v_expr_681_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
return v___x_682_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(lean_object* v_as_683_, size_t v_i_684_, size_t v_stop_685_, lean_object* v_b_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
uint8_t v___x_694_; 
v___x_694_ = lean_usize_dec_eq(v_i_684_, v_stop_685_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_array_uget_borrowed(v_as_683_, v_i_684_);
lean_inc(v___x_695_);
v___x_696_ = l_Lean_Compiler_LCNF_Closure_collectArg(v___x_695_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; size_t v___x_698_; size_t v___x_699_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_696_, 1);
v___x_698_ = ((size_t)1ULL);
v___x_699_ = lean_usize_add(v_i_684_, v___x_698_);
v_i_684_ = v___x_699_;
v_b_686_ = v_a_697_;
goto _start;
}
else
{
return v___x_696_;
}
}
else
{
lean_object* v___x_701_; 
v___x_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_701_, 0, v_b_686_);
return v___x_701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectLetValue(lean_object* v_e_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
switch(lean_obj_tag(v_e_702_))
{
case 2:
{
lean_object* v_struct_710_; lean_object* v___x_711_; 
v_struct_710_ = lean_ctor_get(v_e_702_, 2);
lean_inc(v_struct_710_);
lean_dec_ref_known(v_e_702_, 3);
v___x_711_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v_struct_710_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
return v___x_711_;
}
case 3:
{
lean_object* v_args_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v_args_712_ = lean_ctor_get(v_e_702_, 2);
lean_inc_ref(v_args_712_);
lean_dec_ref_known(v_e_702_, 3);
v___x_713_ = lean_unsigned_to_nat(0u);
v___x_714_ = lean_array_get_size(v_args_712_);
v___x_715_ = lean_box(0);
v___x_716_ = lean_nat_dec_lt(v___x_713_, v___x_714_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
lean_dec_ref(v_args_712_);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_715_);
return v___x_717_;
}
else
{
size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; 
v___x_718_ = ((size_t)0ULL);
v___x_719_ = lean_usize_of_nat(v___x_714_);
v___x_720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_712_, v___x_718_, v___x_719_, v___x_715_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
lean_dec_ref(v_args_712_);
return v___x_720_;
}
}
case 4:
{
lean_object* v_fvarId_721_; lean_object* v_args_722_; lean_object* v___x_723_; 
v_fvarId_721_ = lean_ctor_get(v_e_702_, 0);
lean_inc(v_fvarId_721_);
v_args_722_ = lean_ctor_get(v_e_702_, 1);
lean_inc_ref(v_args_722_);
lean_dec_ref_known(v_e_702_, 2);
v___x_723_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v_fvarId_721_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_737_; 
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_737_ == 0)
{
lean_object* v_unused_738_; 
v_unused_738_ = lean_ctor_get(v___x_723_, 0);
lean_dec(v_unused_738_);
v___x_725_ = v___x_723_;
v_isShared_726_ = v_isSharedCheck_737_;
goto v_resetjp_724_;
}
else
{
lean_dec(v___x_723_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_737_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = lean_array_get_size(v_args_722_);
v___x_729_ = lean_box(0);
v___x_730_ = lean_nat_dec_lt(v___x_727_, v___x_728_);
if (v___x_730_ == 0)
{
lean_object* v___x_732_; 
lean_dec_ref(v_args_722_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_729_);
v___x_732_ = v___x_725_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_729_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
else
{
size_t v___x_734_; size_t v___x_735_; lean_object* v___x_736_; 
lean_del_object(v___x_725_);
v___x_734_ = ((size_t)0ULL);
v___x_735_ = lean_usize_of_nat(v___x_728_);
v___x_736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_722_, v___x_734_, v___x_735_, v___x_729_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
lean_dec_ref(v_args_722_);
return v___x_736_;
}
}
}
else
{
lean_dec_ref(v_args_722_);
return v___x_723_;
}
}
default: 
{
lean_object* v___x_739_; lean_object* v___x_740_; 
lean_dec(v_e_702_);
v___x_739_ = lean_box(0);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
return v___x_740_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11(lean_object* v_as_741_, size_t v_i_742_, size_t v_stop_743_, lean_object* v_b_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v___y_753_; uint8_t v___x_758_; 
v___x_758_ = lean_usize_dec_eq(v_i_742_, v_stop_743_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; 
v___x_759_ = lean_array_uget_borrowed(v_as_741_, v_i_742_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_params_760_; lean_object* v_code_761_; lean_object* v___x_762_; 
v_params_760_ = lean_ctor_get(v___x_759_, 1);
v_code_761_ = lean_ctor_get(v___x_759_, 2);
v___x_762_ = l_Lean_Compiler_LCNF_Closure_collectParams(v_params_760_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v___x_763_; 
lean_dec_ref_known(v___x_762_, 1);
lean_inc_ref(v_code_761_);
v___x_763_ = l_Lean_Compiler_LCNF_Closure_collectCode(v_code_761_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
v___y_753_ = v___x_763_;
goto v___jp_752_;
}
else
{
return v___x_762_;
}
}
else
{
lean_object* v_code_764_; lean_object* v___x_765_; 
v_code_764_ = lean_ctor_get(v___x_759_, 0);
lean_inc_ref(v_code_764_);
v___x_765_ = l_Lean_Compiler_LCNF_Closure_collectCode(v_code_764_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
v___y_753_ = v___x_765_;
goto v___jp_752_;
}
}
else
{
lean_object* v___x_766_; 
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v_b_744_);
return v___x_766_;
}
v___jp_752_:
{
if (lean_obj_tag(v___y_753_) == 0)
{
lean_object* v_a_754_; size_t v___x_755_; size_t v___x_756_; 
v_a_754_ = lean_ctor_get(v___y_753_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v___y_753_, 1);
v___x_755_ = ((size_t)1ULL);
v___x_756_ = lean_usize_add(v_i_742_, v___x_755_);
v_i_742_ = v___x_756_;
v_b_744_ = v_a_754_;
goto _start;
}
else
{
return v___y_753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectCode(lean_object* v_c_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_decl_776_; lean_object* v_k_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; 
switch(lean_obj_tag(v_c_767_))
{
case 0:
{
lean_object* v_decl_786_; lean_object* v_k_787_; lean_object* v_type_788_; lean_object* v_value_789_; lean_object* v___x_790_; 
v_decl_786_ = lean_ctor_get(v_c_767_, 0);
lean_inc_ref(v_decl_786_);
v_k_787_ = lean_ctor_get(v_c_767_, 1);
lean_inc_ref(v_k_787_);
lean_dec_ref_known(v_c_767_, 2);
v_type_788_ = lean_ctor_get(v_decl_786_, 2);
lean_inc_ref(v_type_788_);
v_value_789_ = lean_ctor_get(v_decl_786_, 3);
lean_inc(v_value_789_);
lean_dec_ref(v_decl_786_);
v___x_790_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_788_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v___x_791_; 
lean_dec_ref_known(v___x_790_, 1);
v___x_791_ = l_Lean_Compiler_LCNF_Closure_collectLetValue(v_value_789_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_dec_ref_known(v___x_791_, 1);
v_c_767_ = v_k_787_;
goto _start;
}
else
{
lean_dec_ref(v_k_787_);
return v___x_791_;
}
}
else
{
lean_dec(v_value_789_);
lean_dec_ref(v_k_787_);
return v___x_790_;
}
}
case 3:
{
lean_object* v_args_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v_args_793_ = lean_ctor_get(v_c_767_, 1);
lean_inc_ref(v_args_793_);
lean_dec_ref_known(v_c_767_, 2);
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = lean_array_get_size(v_args_793_);
v___x_796_ = lean_box(0);
v___x_797_ = lean_nat_dec_lt(v___x_794_, v___x_795_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; 
lean_dec_ref(v_args_793_);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_796_);
return v___x_798_;
}
else
{
size_t v___x_799_; size_t v___x_800_; lean_object* v___x_801_; 
v___x_799_ = ((size_t)0ULL);
v___x_800_ = lean_usize_of_nat(v___x_795_);
v___x_801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_793_, v___x_799_, v___x_800_, v___x_796_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
lean_dec_ref(v_args_793_);
return v___x_801_;
}
}
case 4:
{
lean_object* v_cases_802_; lean_object* v_resultType_803_; lean_object* v_discr_804_; lean_object* v_alts_805_; lean_object* v___x_806_; 
v_cases_802_ = lean_ctor_get(v_c_767_, 0);
lean_inc_ref(v_cases_802_);
lean_dec_ref_known(v_c_767_, 1);
v_resultType_803_ = lean_ctor_get(v_cases_802_, 1);
lean_inc_ref(v_resultType_803_);
v_discr_804_ = lean_ctor_get(v_cases_802_, 2);
lean_inc(v_discr_804_);
v_alts_805_ = lean_ctor_get(v_cases_802_, 3);
lean_inc_ref(v_alts_805_);
lean_dec_ref(v_cases_802_);
v___x_806_ = l_Lean_Compiler_LCNF_Closure_collectType(v_resultType_803_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v___x_807_; 
lean_dec_ref_known(v___x_806_, 1);
v___x_807_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v_discr_804_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_821_; 
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v___x_807_, 0);
lean_dec(v_unused_822_);
v___x_809_ = v___x_807_;
v_isShared_810_ = v_isSharedCheck_821_;
goto v_resetjp_808_;
}
else
{
lean_dec(v___x_807_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_821_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_811_ = lean_unsigned_to_nat(0u);
v___x_812_ = lean_array_get_size(v_alts_805_);
v___x_813_ = lean_box(0);
v___x_814_ = lean_nat_dec_lt(v___x_811_, v___x_812_);
if (v___x_814_ == 0)
{
lean_object* v___x_816_; 
lean_dec_ref(v_alts_805_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_813_);
v___x_816_ = v___x_809_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_813_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
else
{
size_t v___x_818_; size_t v___x_819_; lean_object* v___x_820_; 
lean_del_object(v___x_809_);
v___x_818_ = ((size_t)0ULL);
v___x_819_ = lean_usize_of_nat(v___x_812_);
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11(v_alts_805_, v___x_818_, v___x_819_, v___x_813_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
lean_dec_ref(v_alts_805_);
return v___x_820_;
}
}
}
else
{
lean_dec_ref(v_alts_805_);
return v___x_807_;
}
}
else
{
lean_dec_ref(v_alts_805_);
lean_dec(v_discr_804_);
return v___x_806_;
}
}
case 5:
{
lean_object* v_fvarId_823_; lean_object* v___x_824_; 
v_fvarId_823_ = lean_ctor_get(v_c_767_, 0);
lean_inc(v_fvarId_823_);
lean_dec_ref_known(v_c_767_, 1);
v___x_824_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v_fvarId_823_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
return v___x_824_;
}
case 6:
{
lean_object* v_type_825_; lean_object* v___x_826_; 
v_type_825_ = lean_ctor_get(v_c_767_, 0);
lean_inc_ref(v_type_825_);
lean_dec_ref_known(v_c_767_, 1);
v___x_826_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_825_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
return v___x_826_;
}
default: 
{
lean_object* v_decl_827_; lean_object* v_k_828_; 
v_decl_827_ = lean_ctor_get(v_c_767_, 0);
lean_inc_ref(v_decl_827_);
v_k_828_ = lean_ctor_get(v_c_767_, 1);
lean_inc_ref(v_k_828_);
lean_dec_ref(v_c_767_);
v_decl_776_ = v_decl_827_;
v_k_777_ = v_k_828_;
v___y_778_ = v_a_768_;
v___y_779_ = v_a_769_;
v___y_780_ = v_a_770_;
v___y_781_ = v_a_771_;
v___y_782_ = v_a_772_;
v___y_783_ = v_a_773_;
goto v___jp_775_;
}
}
v___jp_775_:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Compiler_LCNF_Closure_collectFunDecl(v_decl_776_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_dec_ref_known(v___x_784_, 1);
v_c_767_ = v_k_777_;
v_a_768_ = v___y_778_;
v_a_769_ = v___y_779_;
v_a_770_ = v___y_780_;
v_a_771_ = v___y_781_;
v_a_772_ = v___y_782_;
v_a_773_ = v___y_783_;
goto _start;
}
else
{
lean_dec_ref(v_k_777_);
return v___x_784_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFunDecl(lean_object* v_decl_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_params_837_; lean_object* v_type_838_; lean_object* v_value_839_; lean_object* v___x_840_; 
v_params_837_ = lean_ctor_get(v_decl_829_, 2);
lean_inc_ref(v_params_837_);
v_type_838_ = lean_ctor_get(v_decl_829_, 3);
lean_inc_ref(v_type_838_);
v_value_839_ = lean_ctor_get(v_decl_829_, 4);
lean_inc_ref(v_value_839_);
lean_dec_ref(v_decl_829_);
v___x_840_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_838_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v___x_841_; 
lean_dec_ref_known(v___x_840_, 1);
v___x_841_ = l_Lean_Compiler_LCNF_Closure_collectParams(v_params_837_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
lean_dec_ref(v_params_837_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v___x_842_; 
lean_dec_ref_known(v___x_841_, 1);
v___x_842_ = l_Lean_Compiler_LCNF_Closure_collectCode(v_value_839_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
return v___x_842_;
}
else
{
lean_dec_ref(v_value_839_);
return v___x_841_;
}
}
else
{
lean_dec_ref(v_value_839_);
lean_dec_ref(v_params_837_);
return v___x_840_;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_846_ = ((lean_object*)(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2));
v___x_847_ = lean_unsigned_to_nat(10u);
v___x_848_ = lean_unsigned_to_nat(149u);
v___x_849_ = ((lean_object*)(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1));
v___x_850_ = ((lean_object*)(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__0));
v___x_851_ = l_mkPanicMessageWithDecl(v___x_850_, v___x_849_, v___x_848_, v___x_847_, v___x_846_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar(lean_object* v_fvarId_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v___x_860_; lean_object* v_visited_861_; uint8_t v___x_862_; 
v___x_860_ = lean_st_ref_get(v_a_854_);
v_visited_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc_ref(v_visited_861_);
lean_dec(v___x_860_);
v___x_862_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg(v_visited_861_, v_fvarId_852_);
lean_dec_ref(v_visited_861_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; 
lean_inc(v_fvarId_852_);
v___x_863_ = l_Lean_Compiler_LCNF_Closure_markVisited___redArg(v_fvarId_852_, v_a_854_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_1052_; 
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; 
v_unused_1053_ = lean_ctor_get(v___x_863_, 0);
lean_dec(v_unused_1053_);
v___x_865_ = v___x_863_;
v_isShared_866_ = v_isSharedCheck_1052_;
goto v_resetjp_864_;
}
else
{
lean_dec(v___x_863_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_1052_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v_inScope_867_; lean_object* v_abstract_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v_inScope_867_ = lean_ctor_get(v_a_853_, 0);
v_abstract_868_ = lean_ctor_get(v_a_853_, 1);
lean_inc_ref(v_inScope_867_);
lean_inc(v_fvarId_852_);
v___x_869_ = lean_apply_1(v_inScope_867_, v_fvarId_852_);
v___x_870_ = lean_unbox(v___x_869_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; lean_object* v___x_873_; 
lean_dec(v_fvarId_852_);
v___x_871_ = lean_box(0);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_871_);
v___x_873_ = v___x_865_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
else
{
uint8_t v___x_875_; lean_object* v___x_876_; 
lean_del_object(v___x_865_);
v___x_875_ = 0;
v___x_876_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_875_, v_fvarId_852_, v_a_856_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_1043_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_1043_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_1043_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
if (lean_obj_tag(v_a_877_) == 1)
{
lean_object* v_val_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_934_; 
lean_dec(v_fvarId_852_);
v_val_881_ = lean_ctor_get(v_a_877_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v_a_877_);
if (v_isSharedCheck_934_ == 0)
{
v___x_883_ = v_a_877_;
v_isShared_884_ = v_isSharedCheck_934_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_val_881_);
lean_dec(v_a_877_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_934_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v_fvarId_885_; lean_object* v_binderName_886_; lean_object* v_type_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v_fvarId_885_ = lean_ctor_get(v_val_881_, 0);
v_binderName_886_ = lean_ctor_get(v_val_881_, 1);
v_type_887_ = lean_ctor_get(v_val_881_, 3);
lean_inc_ref(v_abstract_868_);
lean_inc(v_fvarId_885_);
v___x_888_ = lean_apply_1(v_abstract_868_, v_fvarId_885_);
v___x_889_ = lean_unbox(v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
lean_del_object(v___x_879_);
lean_inc(v_val_881_);
v___x_890_ = l_Lean_Compiler_LCNF_Closure_collectFunDecl(v_val_881_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_914_; 
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; 
v_unused_915_ = lean_ctor_get(v___x_890_, 0);
lean_dec(v_unused_915_);
v___x_892_ = v___x_890_;
v_isShared_893_ = v_isSharedCheck_914_;
goto v_resetjp_891_;
}
else
{
lean_dec(v___x_890_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_914_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; lean_object* v_visited_895_; lean_object* v_params_896_; lean_object* v_decls_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_913_; 
v___x_894_ = lean_st_ref_take(v_a_854_);
v_visited_895_ = lean_ctor_get(v___x_894_, 0);
v_params_896_ = lean_ctor_get(v___x_894_, 1);
v_decls_897_ = lean_ctor_get(v___x_894_, 2);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_913_ == 0)
{
v___x_899_ = v___x_894_;
v_isShared_900_ = v_isSharedCheck_913_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_decls_897_);
lean_inc(v_params_896_);
lean_inc(v_visited_895_);
lean_dec(v___x_894_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_913_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_901_ = lean_box(0);
if (v_isShared_884_ == 0)
{
v___x_903_ = v___x_883_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_val_881_);
v___x_903_ = v_reuseFailAlloc_912_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = lean_array_push(v_decls_897_, v___x_903_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 2, v___x_904_);
v___x_906_ = v___x_899_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_visited_895_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_params_896_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v___x_904_);
v___x_906_ = v_reuseFailAlloc_911_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_907_ = lean_st_ref_put(v_a_854_, v___x_906_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v___x_901_);
v___x_909_ = v___x_892_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_901_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_883_);
lean_dec(v_val_881_);
return v___x_890_;
}
}
else
{
lean_object* v___x_916_; lean_object* v_visited_917_; lean_object* v_params_918_; lean_object* v_decls_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_933_; 
lean_inc_ref(v_type_887_);
lean_inc(v_binderName_886_);
lean_inc(v_fvarId_885_);
lean_del_object(v___x_883_);
lean_dec(v_val_881_);
v___x_916_ = lean_st_ref_take(v_a_854_);
v_visited_917_ = lean_ctor_get(v___x_916_, 0);
v_params_918_ = lean_ctor_get(v___x_916_, 1);
v_decls_919_ = lean_ctor_get(v___x_916_, 2);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_933_ == 0)
{
v___x_921_ = v___x_916_;
v_isShared_922_ = v_isSharedCheck_933_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_decls_919_);
lean_inc(v_params_918_);
lean_inc(v_visited_917_);
lean_dec(v___x_916_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_933_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_923_ = lean_box(0);
v___x_924_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_924_, 0, v_fvarId_885_);
lean_ctor_set(v___x_924_, 1, v_binderName_886_);
lean_ctor_set(v___x_924_, 2, v_type_887_);
lean_ctor_set_uint8(v___x_924_, sizeof(void*)*3, v___x_862_);
v___x_925_ = lean_array_push(v_params_918_, v___x_924_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 1, v___x_925_);
v___x_927_ = v___x_921_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_visited_917_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v___x_925_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_decls_919_);
v___x_927_ = v_reuseFailAlloc_932_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_928_ = lean_st_ref_put(v_a_854_, v___x_927_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_923_);
v___x_930_ = v___x_879_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_923_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
}
else
{
lean_object* v___x_935_; 
lean_del_object(v___x_879_);
lean_dec(v_a_877_);
v___x_935_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v___x_875_, v_fvarId_852_, v_a_856_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_935_, 1);
if (lean_obj_tag(v_a_936_) == 1)
{
lean_object* v_val_937_; lean_object* v_type_938_; lean_object* v___x_939_; 
lean_dec(v_fvarId_852_);
v_val_937_ = lean_ctor_get(v_a_936_, 0);
lean_inc(v_val_937_);
lean_dec_ref_known(v_a_936_, 1);
v_type_938_ = lean_ctor_get(v_val_937_, 2);
lean_inc_ref(v_type_938_);
v___x_939_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_938_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_960_; 
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; 
v_unused_961_ = lean_ctor_get(v___x_939_, 0);
lean_dec(v_unused_961_);
v___x_941_ = v___x_939_;
v_isShared_942_ = v_isSharedCheck_960_;
goto v_resetjp_940_;
}
else
{
lean_dec(v___x_939_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_960_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v_visited_944_; lean_object* v_params_945_; lean_object* v_decls_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_959_; 
v___x_943_ = lean_st_ref_take(v_a_854_);
v_visited_944_ = lean_ctor_get(v___x_943_, 0);
v_params_945_ = lean_ctor_get(v___x_943_, 1);
v_decls_946_ = lean_ctor_get(v___x_943_, 2);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_959_ == 0)
{
v___x_948_ = v___x_943_;
v_isShared_949_ = v_isSharedCheck_959_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_decls_946_);
lean_inc(v_params_945_);
lean_inc(v_visited_944_);
lean_dec(v___x_943_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_959_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_950_ = lean_box(0);
v___x_951_ = lean_array_push(v_params_945_, v_val_937_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v___x_951_);
v___x_953_ = v___x_948_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_visited_944_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_decls_946_);
v___x_953_ = v_reuseFailAlloc_958_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_954_ = lean_st_ref_put(v_a_854_, v___x_953_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_950_);
v___x_956_ = v___x_941_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_950_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
else
{
lean_dec(v_val_937_);
return v___x_939_;
}
}
else
{
lean_object* v___x_962_; 
lean_dec(v_a_936_);
v___x_962_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_875_, v_fvarId_852_, v_a_856_);
lean_dec(v_fvarId_852_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
lean_dec_ref_known(v___x_962_, 1);
if (lean_obj_tag(v_a_963_) == 1)
{
lean_object* v_val_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_1024_; 
v_val_964_ = lean_ctor_get(v_a_963_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_a_963_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_966_ = v_a_963_;
v_isShared_967_ = v_isSharedCheck_1024_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_val_964_);
lean_dec(v_a_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_1024_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v_fvarId_968_; lean_object* v_binderName_969_; lean_object* v_type_970_; lean_object* v_value_971_; lean_object* v___x_972_; 
v_fvarId_968_ = lean_ctor_get(v_val_964_, 0);
v_binderName_969_ = lean_ctor_get(v_val_964_, 1);
v_type_970_ = lean_ctor_get(v_val_964_, 2);
v_value_971_ = lean_ctor_get(v_val_964_, 3);
lean_inc_ref(v_type_970_);
v___x_972_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_970_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_1022_; 
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; 
v_unused_1023_ = lean_ctor_get(v___x_972_, 0);
lean_dec(v_unused_1023_);
v___x_974_ = v___x_972_;
v_isShared_975_ = v_isSharedCheck_1022_;
goto v_resetjp_973_;
}
else
{
lean_dec(v___x_972_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_1022_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_976_; uint8_t v___x_977_; 
lean_inc_ref(v_abstract_868_);
lean_inc(v_fvarId_968_);
v___x_976_ = lean_apply_1(v_abstract_868_, v_fvarId_968_);
v___x_977_ = lean_unbox(v___x_976_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; 
lean_del_object(v___x_974_);
lean_inc(v_value_971_);
v___x_978_ = l_Lean_Compiler_LCNF_Closure_collectLetValue(v_value_971_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1002_; 
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; 
v_unused_1003_ = lean_ctor_get(v___x_978_, 0);
lean_dec(v_unused_1003_);
v___x_980_ = v___x_978_;
v_isShared_981_ = v_isSharedCheck_1002_;
goto v_resetjp_979_;
}
else
{
lean_dec(v___x_978_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1002_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; lean_object* v_visited_983_; lean_object* v_params_984_; lean_object* v_decls_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1001_; 
v___x_982_ = lean_st_ref_take(v_a_854_);
v_visited_983_ = lean_ctor_get(v___x_982_, 0);
v_params_984_ = lean_ctor_get(v___x_982_, 1);
v_decls_985_ = lean_ctor_get(v___x_982_, 2);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_987_ = v___x_982_;
v_isShared_988_ = v_isSharedCheck_1001_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_decls_985_);
lean_inc(v_params_984_);
lean_inc(v_visited_983_);
lean_dec(v___x_982_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1001_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_989_ = lean_box(0);
if (v_isShared_967_ == 0)
{
lean_ctor_set_tag(v___x_966_, 0);
v___x_991_ = v___x_966_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_val_964_);
v___x_991_ = v_reuseFailAlloc_1000_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_992_ = lean_array_push(v_decls_985_, v___x_991_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 2, v___x_992_);
v___x_994_ = v___x_987_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_visited_983_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_params_984_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v___x_992_);
v___x_994_ = v_reuseFailAlloc_999_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = lean_st_ref_put(v_a_854_, v___x_994_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_989_);
v___x_997_ = v___x_980_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_989_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_966_);
lean_dec(v_val_964_);
return v___x_978_;
}
}
else
{
lean_object* v___x_1004_; lean_object* v_visited_1005_; lean_object* v_params_1006_; lean_object* v_decls_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1021_; 
lean_inc_ref(v_type_970_);
lean_inc(v_binderName_969_);
lean_inc(v_fvarId_968_);
lean_del_object(v___x_966_);
lean_dec(v_val_964_);
v___x_1004_ = lean_st_ref_take(v_a_854_);
v_visited_1005_ = lean_ctor_get(v___x_1004_, 0);
v_params_1006_ = lean_ctor_get(v___x_1004_, 1);
v_decls_1007_ = lean_ctor_get(v___x_1004_, 2);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1009_ = v___x_1004_;
v_isShared_1010_ = v_isSharedCheck_1021_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_decls_1007_);
lean_inc(v_params_1006_);
lean_inc(v_visited_1005_);
lean_dec(v___x_1004_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1021_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1011_ = lean_box(0);
v___x_1012_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1012_, 0, v_fvarId_968_);
lean_ctor_set(v___x_1012_, 1, v_binderName_969_);
lean_ctor_set(v___x_1012_, 2, v_type_970_);
lean_ctor_set_uint8(v___x_1012_, sizeof(void*)*3, v___x_862_);
v___x_1013_ = lean_array_push(v_params_1006_, v___x_1012_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v___x_1013_);
v___x_1015_ = v___x_1009_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_visited_1005_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_decls_1007_);
v___x_1015_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1016_ = lean_st_ref_put(v_a_854_, v___x_1015_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_1011_);
v___x_1018_ = v___x_974_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1011_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_966_);
lean_dec(v_val_964_);
return v___x_972_;
}
}
}
else
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
lean_dec(v_a_963_);
v___x_1025_ = lean_obj_once(&l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3, &l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3_once, _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3);
v___x_1026_ = l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5(v___x_1025_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
return v___x_1026_;
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
v_a_1027_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_962_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_962_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec(v_fvarId_852_);
v_a_1035_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_935_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_935_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec(v_fvarId_852_);
v_a_1044_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_876_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_876_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_852_);
return v___x_863_;
}
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec(v_fvarId_852_);
v___x_1054_ = lean_box(0);
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType___lam__0(lean_object* v_e_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = l_Lean_Expr_fvarId_x21(v_e_1056_);
v___x_1065_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v___x_1064_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectArg___boxed(lean_object* v_arg_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_Compiler_LCNF_Closure_collectArg(v_arg_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType___boxed(lean_object* v_type_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFunDecl___boxed(lean_object* v_decl_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Compiler_LCNF_Closure_collectFunDecl(v_decl_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1088_);
lean_dec_ref(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectParams___boxed(lean_object* v_params_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_Compiler_LCNF_Closure_collectParams(v_params_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec_ref(v_params_1093_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7___boxed(lean_object* v_as_1102_, lean_object* v_i_1103_, lean_object* v_stop_1104_, lean_object* v_b_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
size_t v_i_boxed_1113_; size_t v_stop_boxed_1114_; lean_object* v_res_1115_; 
v_i_boxed_1113_ = lean_unbox_usize(v_i_1103_);
lean_dec(v_i_1103_);
v_stop_boxed_1114_ = lean_unbox_usize(v_stop_1104_);
lean_dec(v_stop_1104_);
v_res_1115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_as_1102_, v_i_boxed_1113_, v_stop_boxed_1114_, v_b_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec_ref(v_as_1102_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0___boxed(lean_object* v_as_1116_, lean_object* v_i_1117_, lean_object* v_stop_1118_, lean_object* v_b_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
size_t v_i_boxed_1127_; size_t v_stop_boxed_1128_; lean_object* v_res_1129_; 
v_i_boxed_1127_ = lean_unbox_usize(v_i_1117_);
lean_dec(v_i_1117_);
v_stop_boxed_1128_ = lean_unbox_usize(v_stop_1118_);
lean_dec(v_stop_1118_);
v_res_1129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0(v_as_1116_, v_i_boxed_1127_, v_stop_boxed_1128_, v_b_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec_ref(v_as_1116_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11___boxed(lean_object* v_as_1130_, lean_object* v_i_1131_, lean_object* v_stop_1132_, lean_object* v_b_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
size_t v_i_boxed_1141_; size_t v_stop_boxed_1142_; lean_object* v_res_1143_; 
v_i_boxed_1141_ = lean_unbox_usize(v_i_1131_);
lean_dec(v_i_1131_);
v_stop_boxed_1142_ = lean_unbox_usize(v_stop_1132_);
lean_dec(v_stop_1132_);
v_res_1143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11(v_as_1130_, v_i_boxed_1141_, v_stop_boxed_1142_, v_b_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec_ref(v_as_1130_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectLetValue___boxed(lean_object* v_e_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_Compiler_LCNF_Closure_collectLetValue(v_e_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectCode___boxed(lean_object* v_c_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_Compiler_LCNF_Closure_collectCode(v_c_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar___boxed(lean_object* v_fvarId_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v_fvarId_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
return v_res_1170_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4(lean_object* v_00_u03b2_1171_, lean_object* v_m_1172_, lean_object* v_a_1173_){
_start:
{
uint8_t v___x_1174_; 
v___x_1174_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg(v_m_1172_, v_a_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___boxed(lean_object* v_00_u03b2_1175_, lean_object* v_m_1176_, lean_object* v_a_1177_){
_start:
{
uint8_t v_res_1178_; lean_object* v_r_1179_; 
v_res_1178_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4(v_00_u03b2_1175_, v_m_1176_, v_a_1177_);
lean_dec(v_a_1177_);
lean_dec_ref(v_m_1176_);
v_r_1179_ = lean_box(v_res_1178_);
return v_r_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9(lean_object* v_e_1180_, lean_object* v_a_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg(v_e_1180_, v_a_1181_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___boxed(lean_object* v_e_1190_, lean_object* v_a_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9(v_e_1190_, v_a_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v_a_1191_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10(lean_object* v_e_1200_, lean_object* v_a_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg(v_e_1200_, v_a_1201_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___boxed(lean_object* v_e_1210_, lean_object* v_a_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10(v_e_1210_, v_a_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v_a_1211_);
return v_res_1219_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14(lean_object* v_00_u03b2_1220_, lean_object* v_m_1221_, lean_object* v_a_1222_){
_start:
{
uint8_t v___x_1223_; 
v___x_1223_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg(v_m_1221_, v_a_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___boxed(lean_object* v_00_u03b2_1224_, lean_object* v_m_1225_, lean_object* v_a_1226_){
_start:
{
uint8_t v_res_1227_; lean_object* v_r_1228_; 
v_res_1227_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14(v_00_u03b2_1224_, v_m_1225_, v_a_1226_);
lean_dec_ref(v_a_1226_);
lean_dec_ref(v_m_1225_);
v_r_1228_ = lean_box(v_res_1227_);
return v_r_1228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15(lean_object* v_00_u03b2_1229_, lean_object* v_m_1230_, lean_object* v_a_1231_, lean_object* v_b_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15___redArg(v_m_1230_, v_a_1231_, v_b_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15(lean_object* v_00_u03b2_1234_, lean_object* v_a_1235_, lean_object* v_x_1236_){
_start:
{
uint8_t v___x_1237_; 
v___x_1237_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(v_a_1235_, v_x_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___boxed(lean_object* v_00_u03b2_1238_, lean_object* v_a_1239_, lean_object* v_x_1240_){
_start:
{
uint8_t v_res_1241_; lean_object* v_r_1242_; 
v_res_1241_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15(v_00_u03b2_1238_, v_a_1239_, v_x_1240_);
lean_dec(v_x_1240_);
lean_dec_ref(v_a_1239_);
v_r_1242_ = lean_box(v_res_1241_);
return v_r_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17(lean_object* v_00_u03b2_1243_, lean_object* v_data_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17___redArg(v_data_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18(lean_object* v_00_u03b2_1246_, lean_object* v_i_1247_, lean_object* v_source_1248_, lean_object* v_target_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18___redArg(v_i_1247_, v_source_1248_, v_target_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_1251_, lean_object* v_x_1252_, lean_object* v_x_1253_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18_spec__19___redArg(v_x_1252_, v_x_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(lean_object* v_k_1255_, lean_object* v_t_1256_){
_start:
{
if (lean_obj_tag(v_t_1256_) == 0)
{
lean_object* v_k_1257_; lean_object* v_l_1258_; lean_object* v_r_1259_; uint8_t v___x_1260_; 
v_k_1257_ = lean_ctor_get(v_t_1256_, 1);
v_l_1258_ = lean_ctor_get(v_t_1256_, 3);
v_r_1259_ = lean_ctor_get(v_t_1256_, 4);
v___x_1260_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1255_, v_k_1257_);
switch(v___x_1260_)
{
case 0:
{
v_t_1256_ = v_l_1258_;
goto _start;
}
case 1:
{
uint8_t v___x_1262_; 
v___x_1262_ = 1;
return v___x_1262_;
}
default: 
{
v_t_1256_ = v_r_1259_;
goto _start;
}
}
}
else
{
uint8_t v___x_1264_; 
v___x_1264_ = 0;
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg___boxed(lean_object* v_k_1265_, lean_object* v_t_1266_){
_start:
{
uint8_t v_res_1267_; lean_object* v_r_1268_; 
v_res_1267_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(v_k_1265_, v_t_1266_);
lean_dec(v_t_1266_);
lean_dec(v_k_1265_);
v_r_1268_ = lean_box(v_res_1267_);
return v_r_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(lean_object* v_a_1269_, lean_object* v_as_1270_, size_t v_i_1271_, size_t v_stop_1272_, lean_object* v_b_1273_){
_start:
{
lean_object* v___y_1275_; uint8_t v___x_1279_; 
v___x_1279_ = lean_usize_dec_eq(v_i_1271_, v_stop_1272_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1280_ = lean_array_uget_borrowed(v_as_1270_, v_i_1271_);
v___x_1281_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v___x_1280_);
v___x_1282_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(v___x_1281_, v_a_1269_);
lean_dec(v___x_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; 
lean_inc(v___x_1280_);
v___x_1283_ = lean_array_push(v_b_1273_, v___x_1280_);
v___y_1275_ = v___x_1283_;
goto v___jp_1274_;
}
else
{
v___y_1275_ = v_b_1273_;
goto v___jp_1274_;
}
}
else
{
return v_b_1273_;
}
v___jp_1274_:
{
size_t v___x_1276_; size_t v___x_1277_; 
v___x_1276_ = ((size_t)1ULL);
v___x_1277_ = lean_usize_add(v_i_1271_, v___x_1276_);
v_i_1271_ = v___x_1277_;
v_b_1273_ = v___y_1275_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2___boxed(lean_object* v_a_1284_, lean_object* v_as_1285_, lean_object* v_i_1286_, lean_object* v_stop_1287_, lean_object* v_b_1288_){
_start:
{
size_t v_i_boxed_1289_; size_t v_stop_boxed_1290_; lean_object* v_res_1291_; 
v_i_boxed_1289_ = lean_unbox_usize(v_i_1286_);
lean_dec(v_i_1286_);
v_stop_boxed_1290_ = lean_unbox_usize(v_stop_1287_);
lean_dec(v_stop_1287_);
v_res_1291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(v_a_1284_, v_as_1285_, v_i_boxed_1289_, v_stop_boxed_1290_, v_b_1288_);
lean_dec_ref(v_as_1285_);
lean_dec(v_a_1284_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(lean_object* v_as_1292_, size_t v_sz_1293_, size_t v_i_1294_, lean_object* v_b_1295_){
_start:
{
uint8_t v___x_1297_; 
v___x_1297_ = lean_usize_dec_lt(v_i_1294_, v_sz_1293_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; 
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v_b_1295_);
return v___x_1298_;
}
else
{
lean_object* v_a_1299_; lean_object* v_fvarId_1300_; lean_object* v___x_1301_; size_t v___x_1302_; size_t v___x_1303_; 
v_a_1299_ = lean_array_uget_borrowed(v_as_1292_, v_i_1294_);
v_fvarId_1300_ = lean_ctor_get(v_a_1299_, 0);
lean_inc(v_fvarId_1300_);
v___x_1301_ = l_Lean_FVarIdSet_insert(v_b_1295_, v_fvarId_1300_);
v___x_1302_ = ((size_t)1ULL);
v___x_1303_ = lean_usize_add(v_i_1294_, v___x_1302_);
v_i_1294_ = v___x_1303_;
v_b_1295_ = v___x_1301_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg___boxed(lean_object* v_as_1305_, lean_object* v_sz_1306_, lean_object* v_i_1307_, lean_object* v_b_1308_, lean_object* v___y_1309_){
_start:
{
size_t v_sz_boxed_1310_; size_t v_i_boxed_1311_; lean_object* v_res_1312_; 
v_sz_boxed_1310_ = lean_unbox_usize(v_sz_1306_);
lean_dec(v_sz_1306_);
v_i_boxed_1311_ = lean_unbox_usize(v_i_1307_);
lean_dec(v_i_1307_);
v_res_1312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(v_as_1305_, v_sz_boxed_1310_, v_i_boxed_1311_, v_b_1308_);
lean_dec_ref(v_as_1305_);
return v_res_1312_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1315_ = ((lean_object*)(l_Lean_Compiler_LCNF_Closure_run___redArg___closed__0));
v___x_1316_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_1317_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
lean_ctor_set(v___x_1317_, 1, v___x_1315_);
lean_ctor_set(v___x_1317_, 2, v___x_1315_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run___redArg(lean_object* v_x_1318_, lean_object* v_inScope_1319_, lean_object* v_abstract_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1326_ = lean_box(1);
v___x_1327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1327_, 0, v_inScope_1319_);
lean_ctor_set(v___x_1327_, 1, v_abstract_1320_);
v___x_1328_ = lean_unsigned_to_nat(0u);
v___x_1329_ = ((lean_object*)(l_Lean_Compiler_LCNF_Closure_run___redArg___closed__0));
v___x_1330_ = lean_obj_once(&l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1, &l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1);
v___x_1331_ = lean_st_mk_ref(v___x_1330_);
lean_inc(v_a_1324_);
lean_inc_ref(v_a_1323_);
lean_inc(v_a_1322_);
lean_inc_ref(v_a_1321_);
lean_inc(v___x_1331_);
v___x_1332_ = lean_apply_7(v_x_1318_, v___x_1327_, v___x_1331_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, lean_box(0));
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1334_; lean_object* v_params_1335_; lean_object* v_decls_1336_; size_t v_sz_1337_; size_t v___x_1338_; lean_object* v___x_1339_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
lean_dec_ref_known(v___x_1332_, 1);
v___x_1334_ = lean_st_ref_get(v___x_1331_);
lean_dec(v___x_1331_);
v_params_1335_ = lean_ctor_get(v___x_1334_, 1);
lean_inc_ref(v_params_1335_);
v_decls_1336_ = lean_ctor_get(v___x_1334_, 2);
lean_inc_ref(v_decls_1336_);
lean_dec(v___x_1334_);
v_sz_1337_ = lean_array_size(v_params_1335_);
v___x_1338_ = ((size_t)0ULL);
v___x_1339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(v_params_1335_, v_sz_1337_, v___x_1338_, v___x_1326_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1355_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1342_ = v___x_1339_;
v_isShared_1343_ = v_isSharedCheck_1355_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1339_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1355_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___y_1345_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1351_ = lean_array_get_size(v_decls_1336_);
v___x_1352_ = lean_nat_dec_lt(v___x_1328_, v___x_1351_);
if (v___x_1352_ == 0)
{
lean_dec(v_a_1340_);
lean_dec_ref(v_decls_1336_);
v___y_1345_ = v___x_1329_;
goto v___jp_1344_;
}
else
{
size_t v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = lean_usize_of_nat(v___x_1351_);
v___x_1354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(v_a_1340_, v_decls_1336_, v___x_1338_, v___x_1353_, v___x_1329_);
lean_dec_ref(v_decls_1336_);
lean_dec(v_a_1340_);
v___y_1345_ = v___x_1354_;
goto v___jp_1344_;
}
v___jp_1344_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v_params_1335_);
lean_ctor_set(v___x_1346_, 1, v___y_1345_);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v_a_1333_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1347_);
v___x_1349_ = v___x_1342_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec_ref(v_decls_1336_);
lean_dec_ref(v_params_1335_);
lean_dec(v_a_1333_);
v_a_1356_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1339_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1339_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec(v___x_1331_);
v_a_1364_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1332_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1332_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run___redArg___boxed(lean_object* v_x_1372_, lean_object* v_inScope_1373_, lean_object* v_abstract_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Lean_Compiler_LCNF_Closure_run___redArg(v_x_1372_, v_inScope_1373_, v_abstract_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run(lean_object* v_00_u03b1_1381_, lean_object* v_x_1382_, lean_object* v_inScope_1383_, lean_object* v_abstract_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_Compiler_LCNF_Closure_run___redArg(v_x_1382_, v_inScope_1383_, v_abstract_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run___boxed(lean_object* v_00_u03b1_1391_, lean_object* v_x_1392_, lean_object* v_inScope_1393_, lean_object* v_abstract_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_Compiler_LCNF_Closure_run(v_00_u03b1_1391_, v_x_1392_, v_inScope_1393_, v_abstract_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0(lean_object* v_as_1401_, size_t v_sz_1402_, size_t v_i_1403_, lean_object* v_b_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(v_as_1401_, v_sz_1402_, v_i_1403_, v_b_1404_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___boxed(lean_object* v_as_1411_, lean_object* v_sz_1412_, lean_object* v_i_1413_, lean_object* v_b_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
size_t v_sz_boxed_1420_; size_t v_i_boxed_1421_; lean_object* v_res_1422_; 
v_sz_boxed_1420_ = lean_unbox_usize(v_sz_1412_);
lean_dec(v_sz_1412_);
v_i_boxed_1421_ = lean_unbox_usize(v_i_1413_);
lean_dec(v_i_1413_);
v_res_1422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0(v_as_1411_, v_sz_boxed_1420_, v_i_boxed_1421_, v_b_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec_ref(v_as_1411_);
return v_res_1422_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1(lean_object* v_00_u03b2_1423_, lean_object* v_k_1424_, lean_object* v_t_1425_){
_start:
{
uint8_t v___x_1426_; 
v___x_1426_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(v_k_1424_, v_t_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___boxed(lean_object* v_00_u03b2_1427_, lean_object* v_k_1428_, lean_object* v_t_1429_){
_start:
{
uint8_t v_res_1430_; lean_object* v_r_1431_; 
v_res_1430_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1(v_00_u03b2_1427_, v_k_1428_, v_t_1429_);
lean_dec(v_t_1429_);
lean_dec(v_k_1428_);
v_r_1431_ = lean_box(v_res_1430_);
return v_r_1431_;
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
