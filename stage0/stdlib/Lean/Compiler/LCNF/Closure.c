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
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___f_235_; lean_object* v___x_20013__overap_236_; lean_object* v___x_237_; 
v___x_232_ = l_StateRefT_x27_instMonad___redArg(v___x_231_);
v___x_233_ = lean_box(0);
v___x_234_ = l_instInhabitedOfMonad___redArg(v___x_232_, v___x_233_);
v___f_235_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_235_, 0, v___x_234_);
v___x_20013__overap_236_ = lean_panic_fn_borrowed(v___f_235_, v_msg_175_);
lean_dec_ref(v___f_235_);
lean_inc(v___y_181_);
lean_inc_ref(v___y_180_);
lean_inc(v___y_179_);
lean_inc_ref(v___y_178_);
lean_inc(v___y_177_);
lean_inc_ref(v___y_176_);
v___x_237_ = lean_apply_7(v___x_20013__overap_236_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, lean_box(0));
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
v___x_464_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4(v_p_442_, v_f_443_, v_stopWhenVisited_444_, v_d_461_, v___y_463_, v___y_455_, v___y_457_, v___y_460_, v___y_458_, v___y_459_, v___y_456_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_dec_ref_known(v___x_464_, 1);
v_e_445_ = v_b_462_;
v_a_446_ = v___y_463_;
v___y_447_ = v___y_455_;
v___y_448_ = v___y_457_;
v___y_449_ = v___y_460_;
v___y_450_ = v___y_458_;
v___y_451_ = v___y_459_;
v___y_452_ = v___y_456_;
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
v___y_455_ = v___y_468_;
v___y_456_ = v___y_473_;
v___y_457_ = v___y_469_;
v___y_458_ = v___y_471_;
v___y_459_ = v___y_472_;
v___y_460_ = v___y_470_;
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
v___y_455_ = v___y_468_;
v___y_456_ = v___y_473_;
v___y_457_ = v___y_469_;
v___y_458_ = v___y_471_;
v___y_459_ = v___y_472_;
v___y_460_ = v___y_470_;
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
uint8_t v___x_666_; 
v___x_666_ = lean_nat_dec_le(v___x_662_, v___x_662_);
if (v___x_666_ == 0)
{
if (v___x_664_ == 0)
{
lean_object* v___x_667_; 
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_663_);
return v___x_667_;
}
else
{
size_t v___x_668_; size_t v___x_669_; lean_object* v___x_670_; 
v___x_668_ = ((size_t)0ULL);
v___x_669_ = lean_usize_of_nat(v___x_662_);
v___x_670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0(v_params_653_, v___x_668_, v___x_669_, v___x_663_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
return v___x_670_;
}
}
else
{
size_t v___x_671_; size_t v___x_672_; lean_object* v___x_673_; 
v___x_671_ = ((size_t)0ULL);
v___x_672_ = lean_usize_of_nat(v___x_662_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0(v_params_653_, v___x_671_, v___x_672_, v___x_663_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
return v___x_673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectArg(lean_object* v_arg_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
switch(lean_obj_tag(v_arg_674_))
{
case 0:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_box(0);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
case 1:
{
lean_object* v_fvarId_684_; lean_object* v___x_685_; 
v_fvarId_684_ = lean_ctor_get(v_arg_674_, 0);
lean_inc(v_fvarId_684_);
lean_dec_ref_known(v_arg_674_, 1);
v___x_685_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v_fvarId_684_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
return v___x_685_;
}
default: 
{
lean_object* v_expr_686_; lean_object* v___x_687_; 
v_expr_686_ = lean_ctor_get(v_arg_674_, 0);
lean_inc_ref(v_expr_686_);
lean_dec_ref_known(v_arg_674_, 1);
v___x_687_ = l_Lean_Compiler_LCNF_Closure_collectType(v_expr_686_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
return v___x_687_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(lean_object* v_as_688_, size_t v_i_689_, size_t v_stop_690_, lean_object* v_b_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
uint8_t v___x_699_; 
v___x_699_ = lean_usize_dec_eq(v_i_689_, v_stop_690_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_array_uget_borrowed(v_as_688_, v_i_689_);
lean_inc(v___x_700_);
v___x_701_ = l_Lean_Compiler_LCNF_Closure_collectArg(v___x_700_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; size_t v___x_703_; size_t v___x_704_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v___x_701_, 1);
v___x_703_ = ((size_t)1ULL);
v___x_704_ = lean_usize_add(v_i_689_, v___x_703_);
v_i_689_ = v___x_704_;
v_b_691_ = v_a_702_;
goto _start;
}
else
{
return v___x_701_;
}
}
else
{
lean_object* v___x_706_; 
v___x_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_706_, 0, v_b_691_);
return v___x_706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectLetValue(lean_object* v_e_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
switch(lean_obj_tag(v_e_707_))
{
case 2:
{
lean_object* v_struct_715_; lean_object* v___x_716_; 
v_struct_715_ = lean_ctor_get(v_e_707_, 2);
lean_inc(v_struct_715_);
lean_dec_ref_known(v_e_707_, 3);
v___x_716_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v_struct_715_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
return v___x_716_;
}
case 3:
{
lean_object* v_args_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v_args_717_ = lean_ctor_get(v_e_707_, 2);
lean_inc_ref(v_args_717_);
lean_dec_ref_known(v_e_707_, 3);
v___x_718_ = lean_unsigned_to_nat(0u);
v___x_719_ = lean_array_get_size(v_args_717_);
v___x_720_ = lean_box(0);
v___x_721_ = lean_nat_dec_lt(v___x_718_, v___x_719_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
lean_dec_ref(v_args_717_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_720_);
return v___x_722_;
}
else
{
uint8_t v___x_723_; 
v___x_723_ = lean_nat_dec_le(v___x_719_, v___x_719_);
if (v___x_723_ == 0)
{
if (v___x_721_ == 0)
{
lean_object* v___x_724_; 
lean_dec_ref(v_args_717_);
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_720_);
return v___x_724_;
}
else
{
size_t v___x_725_; size_t v___x_726_; lean_object* v___x_727_; 
v___x_725_ = ((size_t)0ULL);
v___x_726_ = lean_usize_of_nat(v___x_719_);
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_717_, v___x_725_, v___x_726_, v___x_720_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
lean_dec_ref(v_args_717_);
return v___x_727_;
}
}
else
{
size_t v___x_728_; size_t v___x_729_; lean_object* v___x_730_; 
v___x_728_ = ((size_t)0ULL);
v___x_729_ = lean_usize_of_nat(v___x_719_);
v___x_730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_717_, v___x_728_, v___x_729_, v___x_720_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
lean_dec_ref(v_args_717_);
return v___x_730_;
}
}
}
case 4:
{
lean_object* v_fvarId_731_; lean_object* v_args_732_; lean_object* v___x_733_; 
v_fvarId_731_ = lean_ctor_get(v_e_707_, 0);
lean_inc(v_fvarId_731_);
v_args_732_ = lean_ctor_get(v_e_707_, 1);
lean_inc_ref(v_args_732_);
lean_dec_ref_known(v_e_707_, 2);
v___x_733_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v_fvarId_731_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_754_; 
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; 
v_unused_755_ = lean_ctor_get(v___x_733_, 0);
lean_dec(v_unused_755_);
v___x_735_ = v___x_733_;
v_isShared_736_ = v_isSharedCheck_754_;
goto v_resetjp_734_;
}
else
{
lean_dec(v___x_733_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_754_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = lean_array_get_size(v_args_732_);
v___x_739_ = lean_box(0);
v___x_740_ = lean_nat_dec_lt(v___x_737_, v___x_738_);
if (v___x_740_ == 0)
{
lean_object* v___x_742_; 
lean_dec_ref(v_args_732_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_739_);
v___x_742_ = v___x_735_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_739_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
else
{
uint8_t v___x_744_; 
v___x_744_ = lean_nat_dec_le(v___x_738_, v___x_738_);
if (v___x_744_ == 0)
{
if (v___x_740_ == 0)
{
lean_object* v___x_746_; 
lean_dec_ref(v_args_732_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_739_);
v___x_746_ = v___x_735_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_739_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
else
{
size_t v___x_748_; size_t v___x_749_; lean_object* v___x_750_; 
lean_del_object(v___x_735_);
v___x_748_ = ((size_t)0ULL);
v___x_749_ = lean_usize_of_nat(v___x_738_);
v___x_750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_732_, v___x_748_, v___x_749_, v___x_739_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
lean_dec_ref(v_args_732_);
return v___x_750_;
}
}
else
{
size_t v___x_751_; size_t v___x_752_; lean_object* v___x_753_; 
lean_del_object(v___x_735_);
v___x_751_ = ((size_t)0ULL);
v___x_752_ = lean_usize_of_nat(v___x_738_);
v___x_753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_732_, v___x_751_, v___x_752_, v___x_739_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
lean_dec_ref(v_args_732_);
return v___x_753_;
}
}
}
}
else
{
lean_dec_ref(v_args_732_);
return v___x_733_;
}
}
default: 
{
lean_object* v___x_756_; lean_object* v___x_757_; 
lean_dec(v_e_707_);
v___x_756_ = lean_box(0);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11(lean_object* v_as_758_, size_t v_i_759_, size_t v_stop_760_, lean_object* v_b_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v___y_770_; uint8_t v___x_775_; 
v___x_775_ = lean_usize_dec_eq(v_i_759_, v_stop_760_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
v___x_776_ = lean_array_uget_borrowed(v_as_758_, v_i_759_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_params_777_; lean_object* v_code_778_; lean_object* v___x_779_; 
v_params_777_ = lean_ctor_get(v___x_776_, 1);
v_code_778_ = lean_ctor_get(v___x_776_, 2);
v___x_779_ = l_Lean_Compiler_LCNF_Closure_collectParams(v_params_777_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v___x_780_; 
lean_dec_ref_known(v___x_779_, 1);
lean_inc_ref(v_code_778_);
v___x_780_ = l_Lean_Compiler_LCNF_Closure_collectCode(v_code_778_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
v___y_770_ = v___x_780_;
goto v___jp_769_;
}
else
{
v___y_770_ = v___x_779_;
goto v___jp_769_;
}
}
else
{
lean_object* v_code_781_; lean_object* v___x_782_; 
v_code_781_ = lean_ctor_get(v___x_776_, 0);
lean_inc_ref(v_code_781_);
v___x_782_ = l_Lean_Compiler_LCNF_Closure_collectCode(v_code_781_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
v___y_770_ = v___x_782_;
goto v___jp_769_;
}
}
else
{
lean_object* v___x_783_; 
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v_b_761_);
return v___x_783_;
}
v___jp_769_:
{
if (lean_obj_tag(v___y_770_) == 0)
{
lean_object* v_a_771_; size_t v___x_772_; size_t v___x_773_; 
v_a_771_ = lean_ctor_get(v___y_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref_known(v___y_770_, 1);
v___x_772_ = ((size_t)1ULL);
v___x_773_ = lean_usize_add(v_i_759_, v___x_772_);
v_i_759_ = v___x_773_;
v_b_761_ = v_a_771_;
goto _start;
}
else
{
return v___y_770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectCode(lean_object* v_c_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_decl_793_; lean_object* v_k_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; 
switch(lean_obj_tag(v_c_784_))
{
case 0:
{
lean_object* v_decl_803_; lean_object* v_k_804_; lean_object* v_type_805_; lean_object* v_value_806_; lean_object* v___x_807_; 
v_decl_803_ = lean_ctor_get(v_c_784_, 0);
lean_inc_ref(v_decl_803_);
v_k_804_ = lean_ctor_get(v_c_784_, 1);
lean_inc_ref(v_k_804_);
lean_dec_ref_known(v_c_784_, 2);
v_type_805_ = lean_ctor_get(v_decl_803_, 2);
lean_inc_ref(v_type_805_);
v_value_806_ = lean_ctor_get(v_decl_803_, 3);
lean_inc(v_value_806_);
lean_dec_ref(v_decl_803_);
v___x_807_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_805_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v___x_808_; 
lean_dec_ref_known(v___x_807_, 1);
v___x_808_ = l_Lean_Compiler_LCNF_Closure_collectLetValue(v_value_806_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_dec_ref_known(v___x_808_, 1);
v_c_784_ = v_k_804_;
goto _start;
}
else
{
lean_dec_ref(v_k_804_);
return v___x_808_;
}
}
else
{
lean_dec(v_value_806_);
lean_dec_ref(v_k_804_);
return v___x_807_;
}
}
case 3:
{
lean_object* v_args_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v_args_810_ = lean_ctor_get(v_c_784_, 1);
lean_inc_ref(v_args_810_);
lean_dec_ref_known(v_c_784_, 2);
v___x_811_ = lean_unsigned_to_nat(0u);
v___x_812_ = lean_array_get_size(v_args_810_);
v___x_813_ = lean_box(0);
v___x_814_ = lean_nat_dec_lt(v___x_811_, v___x_812_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; 
lean_dec_ref(v_args_810_);
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
return v___x_815_;
}
else
{
uint8_t v___x_816_; 
v___x_816_ = lean_nat_dec_le(v___x_812_, v___x_812_);
if (v___x_816_ == 0)
{
if (v___x_814_ == 0)
{
lean_object* v___x_817_; 
lean_dec_ref(v_args_810_);
v___x_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_813_);
return v___x_817_;
}
else
{
size_t v___x_818_; size_t v___x_819_; lean_object* v___x_820_; 
v___x_818_ = ((size_t)0ULL);
v___x_819_ = lean_usize_of_nat(v___x_812_);
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_810_, v___x_818_, v___x_819_, v___x_813_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
lean_dec_ref(v_args_810_);
return v___x_820_;
}
}
else
{
size_t v___x_821_; size_t v___x_822_; lean_object* v___x_823_; 
v___x_821_ = ((size_t)0ULL);
v___x_822_ = lean_usize_of_nat(v___x_812_);
v___x_823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_args_810_, v___x_821_, v___x_822_, v___x_813_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
lean_dec_ref(v_args_810_);
return v___x_823_;
}
}
}
case 4:
{
lean_object* v_cases_824_; lean_object* v_resultType_825_; lean_object* v_discr_826_; lean_object* v_alts_827_; lean_object* v___x_828_; 
v_cases_824_ = lean_ctor_get(v_c_784_, 0);
lean_inc_ref(v_cases_824_);
lean_dec_ref_known(v_c_784_, 1);
v_resultType_825_ = lean_ctor_get(v_cases_824_, 1);
lean_inc_ref(v_resultType_825_);
v_discr_826_ = lean_ctor_get(v_cases_824_, 2);
lean_inc(v_discr_826_);
v_alts_827_ = lean_ctor_get(v_cases_824_, 3);
lean_inc_ref(v_alts_827_);
lean_dec_ref(v_cases_824_);
v___x_828_ = l_Lean_Compiler_LCNF_Closure_collectType(v_resultType_825_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v___x_829_; 
lean_dec_ref_known(v___x_828_, 1);
v___x_829_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v_discr_826_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_850_; 
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; 
v_unused_851_ = lean_ctor_get(v___x_829_, 0);
lean_dec(v_unused_851_);
v___x_831_ = v___x_829_;
v_isShared_832_ = v_isSharedCheck_850_;
goto v_resetjp_830_;
}
else
{
lean_dec(v___x_829_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_850_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = lean_array_get_size(v_alts_827_);
v___x_835_ = lean_box(0);
v___x_836_ = lean_nat_dec_lt(v___x_833_, v___x_834_);
if (v___x_836_ == 0)
{
lean_object* v___x_838_; 
lean_dec_ref(v_alts_827_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_835_);
v___x_838_ = v___x_831_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_835_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
else
{
uint8_t v___x_840_; 
v___x_840_ = lean_nat_dec_le(v___x_834_, v___x_834_);
if (v___x_840_ == 0)
{
if (v___x_836_ == 0)
{
lean_object* v___x_842_; 
lean_dec_ref(v_alts_827_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_835_);
v___x_842_ = v___x_831_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_835_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
else
{
size_t v___x_844_; size_t v___x_845_; lean_object* v___x_846_; 
lean_del_object(v___x_831_);
v___x_844_ = ((size_t)0ULL);
v___x_845_ = lean_usize_of_nat(v___x_834_);
v___x_846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11(v_alts_827_, v___x_844_, v___x_845_, v___x_835_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
lean_dec_ref(v_alts_827_);
return v___x_846_;
}
}
else
{
size_t v___x_847_; size_t v___x_848_; lean_object* v___x_849_; 
lean_del_object(v___x_831_);
v___x_847_ = ((size_t)0ULL);
v___x_848_ = lean_usize_of_nat(v___x_834_);
v___x_849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11(v_alts_827_, v___x_847_, v___x_848_, v___x_835_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
lean_dec_ref(v_alts_827_);
return v___x_849_;
}
}
}
}
else
{
lean_dec_ref(v_alts_827_);
return v___x_829_;
}
}
else
{
lean_dec_ref(v_alts_827_);
lean_dec(v_discr_826_);
return v___x_828_;
}
}
case 5:
{
lean_object* v_fvarId_852_; lean_object* v___x_853_; 
v_fvarId_852_ = lean_ctor_get(v_c_784_, 0);
lean_inc(v_fvarId_852_);
lean_dec_ref_known(v_c_784_, 1);
v___x_853_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v_fvarId_852_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
return v___x_853_;
}
case 6:
{
lean_object* v_type_854_; lean_object* v___x_855_; 
v_type_854_ = lean_ctor_get(v_c_784_, 0);
lean_inc_ref(v_type_854_);
lean_dec_ref_known(v_c_784_, 1);
v___x_855_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_854_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
return v___x_855_;
}
default: 
{
lean_object* v_decl_856_; lean_object* v_k_857_; 
v_decl_856_ = lean_ctor_get(v_c_784_, 0);
lean_inc_ref(v_decl_856_);
v_k_857_ = lean_ctor_get(v_c_784_, 1);
lean_inc_ref(v_k_857_);
lean_dec_ref(v_c_784_);
v_decl_793_ = v_decl_856_;
v_k_794_ = v_k_857_;
v___y_795_ = v_a_785_;
v___y_796_ = v_a_786_;
v___y_797_ = v_a_787_;
v___y_798_ = v_a_788_;
v___y_799_ = v_a_789_;
v___y_800_ = v_a_790_;
goto v___jp_792_;
}
}
v___jp_792_:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_Compiler_LCNF_Closure_collectFunDecl(v_decl_793_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_dec_ref_known(v___x_801_, 1);
v_c_784_ = v_k_794_;
v_a_785_ = v___y_795_;
v_a_786_ = v___y_796_;
v_a_787_ = v___y_797_;
v_a_788_ = v___y_798_;
v_a_789_ = v___y_799_;
v_a_790_ = v___y_800_;
goto _start;
}
else
{
lean_dec_ref(v_k_794_);
return v___x_801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFunDecl(lean_object* v_decl_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_params_866_; lean_object* v_type_867_; lean_object* v_value_868_; lean_object* v___x_869_; 
v_params_866_ = lean_ctor_get(v_decl_858_, 2);
lean_inc_ref(v_params_866_);
v_type_867_ = lean_ctor_get(v_decl_858_, 3);
lean_inc_ref(v_type_867_);
v_value_868_ = lean_ctor_get(v_decl_858_, 4);
lean_inc_ref(v_value_868_);
lean_dec_ref(v_decl_858_);
v___x_869_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_867_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v___x_870_; 
lean_dec_ref_known(v___x_869_, 1);
v___x_870_ = l_Lean_Compiler_LCNF_Closure_collectParams(v_params_866_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
lean_dec_ref(v_params_866_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v___x_871_; 
lean_dec_ref_known(v___x_870_, 1);
v___x_871_ = l_Lean_Compiler_LCNF_Closure_collectCode(v_value_868_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
return v___x_871_;
}
else
{
lean_dec_ref(v_value_868_);
return v___x_870_;
}
}
else
{
lean_dec_ref(v_value_868_);
lean_dec_ref(v_params_866_);
return v___x_869_;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_875_ = ((lean_object*)(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__2));
v___x_876_ = lean_unsigned_to_nat(10u);
v___x_877_ = lean_unsigned_to_nat(149u);
v___x_878_ = ((lean_object*)(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__1));
v___x_879_ = ((lean_object*)(l_Lean_Compiler_LCNF_Closure_collectFVar___closed__0));
v___x_880_ = l_mkPanicMessageWithDecl(v___x_879_, v___x_878_, v___x_877_, v___x_876_, v___x_875_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar(lean_object* v_fvarId_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v___x_889_; lean_object* v_visited_890_; uint8_t v___x_891_; 
v___x_889_ = lean_st_ref_get(v_a_883_);
v_visited_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc_ref(v_visited_890_);
lean_dec(v___x_889_);
v___x_891_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg(v_visited_890_, v_fvarId_881_);
lean_dec_ref(v_visited_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; 
lean_inc(v_fvarId_881_);
v___x_892_ = l_Lean_Compiler_LCNF_Closure_markVisited___redArg(v_fvarId_881_, v_a_883_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_1081_; 
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; 
v_unused_1082_ = lean_ctor_get(v___x_892_, 0);
lean_dec(v_unused_1082_);
v___x_894_ = v___x_892_;
v_isShared_895_ = v_isSharedCheck_1081_;
goto v_resetjp_893_;
}
else
{
lean_dec(v___x_892_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_1081_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v_inScope_896_; lean_object* v_abstract_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v_inScope_896_ = lean_ctor_get(v_a_882_, 0);
v_abstract_897_ = lean_ctor_get(v_a_882_, 1);
lean_inc_ref(v_inScope_896_);
lean_inc(v_fvarId_881_);
v___x_898_ = lean_apply_1(v_inScope_896_, v_fvarId_881_);
v___x_899_ = lean_unbox(v___x_898_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; lean_object* v___x_902_; 
lean_dec(v_fvarId_881_);
v___x_900_ = lean_box(0);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_900_);
v___x_902_ = v___x_894_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
else
{
uint8_t v___x_904_; lean_object* v___x_905_; 
lean_del_object(v___x_894_);
v___x_904_ = 0;
v___x_905_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_904_, v_fvarId_881_, v_a_885_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_1072_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_1072_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_1072_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
if (lean_obj_tag(v_a_906_) == 1)
{
lean_object* v_val_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_963_; 
lean_dec(v_fvarId_881_);
v_val_910_ = lean_ctor_get(v_a_906_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v_a_906_);
if (v_isSharedCheck_963_ == 0)
{
v___x_912_ = v_a_906_;
v_isShared_913_ = v_isSharedCheck_963_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_val_910_);
lean_dec(v_a_906_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_963_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_fvarId_914_; lean_object* v_binderName_915_; lean_object* v_type_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v_fvarId_914_ = lean_ctor_get(v_val_910_, 0);
v_binderName_915_ = lean_ctor_get(v_val_910_, 1);
v_type_916_ = lean_ctor_get(v_val_910_, 3);
lean_inc_ref(v_abstract_897_);
lean_inc(v_fvarId_914_);
v___x_917_ = lean_apply_1(v_abstract_897_, v_fvarId_914_);
v___x_918_ = lean_unbox(v___x_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; 
lean_del_object(v___x_908_);
lean_inc(v_val_910_);
v___x_919_ = l_Lean_Compiler_LCNF_Closure_collectFunDecl(v_val_910_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_943_; 
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_943_ == 0)
{
lean_object* v_unused_944_; 
v_unused_944_ = lean_ctor_get(v___x_919_, 0);
lean_dec(v_unused_944_);
v___x_921_ = v___x_919_;
v_isShared_922_ = v_isSharedCheck_943_;
goto v_resetjp_920_;
}
else
{
lean_dec(v___x_919_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_943_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v_visited_924_; lean_object* v_params_925_; lean_object* v_decls_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_942_; 
v___x_923_ = lean_st_ref_take(v_a_883_);
v_visited_924_ = lean_ctor_get(v___x_923_, 0);
v_params_925_ = lean_ctor_get(v___x_923_, 1);
v_decls_926_ = lean_ctor_get(v___x_923_, 2);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_942_ == 0)
{
v___x_928_ = v___x_923_;
v_isShared_929_ = v_isSharedCheck_942_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_decls_926_);
lean_inc(v_params_925_);
lean_inc(v_visited_924_);
lean_dec(v___x_923_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_942_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_930_ = lean_box(0);
if (v_isShared_913_ == 0)
{
v___x_932_ = v___x_912_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_val_910_);
v___x_932_ = v_reuseFailAlloc_941_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_933_ = lean_array_push(v_decls_926_, v___x_932_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 2, v___x_933_);
v___x_935_ = v___x_928_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_visited_924_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_params_925_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v___x_933_);
v___x_935_ = v_reuseFailAlloc_940_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = lean_st_ref_put(v_a_883_, v___x_935_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_930_);
v___x_938_ = v___x_921_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_930_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_912_);
lean_dec(v_val_910_);
return v___x_919_;
}
}
else
{
lean_object* v___x_945_; lean_object* v_visited_946_; lean_object* v_params_947_; lean_object* v_decls_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_962_; 
lean_inc_ref(v_type_916_);
lean_inc(v_binderName_915_);
lean_inc(v_fvarId_914_);
lean_del_object(v___x_912_);
lean_dec(v_val_910_);
v___x_945_ = lean_st_ref_take(v_a_883_);
v_visited_946_ = lean_ctor_get(v___x_945_, 0);
v_params_947_ = lean_ctor_get(v___x_945_, 1);
v_decls_948_ = lean_ctor_get(v___x_945_, 2);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_962_ == 0)
{
v___x_950_ = v___x_945_;
v_isShared_951_ = v_isSharedCheck_962_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_decls_948_);
lean_inc(v_params_947_);
lean_inc(v_visited_946_);
lean_dec(v___x_945_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_962_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_952_ = lean_box(0);
v___x_953_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_953_, 0, v_fvarId_914_);
lean_ctor_set(v___x_953_, 1, v_binderName_915_);
lean_ctor_set(v___x_953_, 2, v_type_916_);
lean_ctor_set_uint8(v___x_953_, sizeof(void*)*3, v___x_891_);
v___x_954_ = lean_array_push(v_params_947_, v___x_953_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 1, v___x_954_);
v___x_956_ = v___x_950_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_visited_946_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v___x_954_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v_decls_948_);
v___x_956_ = v_reuseFailAlloc_961_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_957_ = lean_st_ref_put(v_a_883_, v___x_956_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_952_);
v___x_959_ = v___x_908_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_952_);
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
lean_object* v___x_964_; 
lean_del_object(v___x_908_);
lean_dec(v_a_906_);
v___x_964_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v___x_904_, v_fvarId_881_, v_a_885_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_964_, 1);
if (lean_obj_tag(v_a_965_) == 1)
{
lean_object* v_val_966_; lean_object* v_type_967_; lean_object* v___x_968_; 
lean_dec(v_fvarId_881_);
v_val_966_ = lean_ctor_get(v_a_965_, 0);
lean_inc(v_val_966_);
lean_dec_ref_known(v_a_965_, 1);
v_type_967_ = lean_ctor_get(v_val_966_, 2);
lean_inc_ref(v_type_967_);
v___x_968_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_967_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_989_; 
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_989_ == 0)
{
lean_object* v_unused_990_; 
v_unused_990_ = lean_ctor_get(v___x_968_, 0);
lean_dec(v_unused_990_);
v___x_970_ = v___x_968_;
v_isShared_971_ = v_isSharedCheck_989_;
goto v_resetjp_969_;
}
else
{
lean_dec(v___x_968_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_989_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v_visited_973_; lean_object* v_params_974_; lean_object* v_decls_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_988_; 
v___x_972_ = lean_st_ref_take(v_a_883_);
v_visited_973_ = lean_ctor_get(v___x_972_, 0);
v_params_974_ = lean_ctor_get(v___x_972_, 1);
v_decls_975_ = lean_ctor_get(v___x_972_, 2);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_988_ == 0)
{
v___x_977_ = v___x_972_;
v_isShared_978_ = v_isSharedCheck_988_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_decls_975_);
lean_inc(v_params_974_);
lean_inc(v_visited_973_);
lean_dec(v___x_972_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_988_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_979_ = lean_box(0);
v___x_980_ = lean_array_push(v_params_974_, v_val_966_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 1, v___x_980_);
v___x_982_ = v___x_977_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_visited_973_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v_decls_975_);
v___x_982_ = v_reuseFailAlloc_987_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_983_ = lean_st_ref_put(v_a_883_, v___x_982_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_979_);
v___x_985_ = v___x_970_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_979_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
else
{
lean_dec(v_val_966_);
return v___x_968_;
}
}
else
{
lean_object* v___x_991_; 
lean_dec(v_a_965_);
v___x_991_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_904_, v_fvarId_881_, v_a_885_);
lean_dec(v_fvarId_881_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_991_, 1);
if (lean_obj_tag(v_a_992_) == 1)
{
lean_object* v_val_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1053_; 
v_val_993_ = lean_ctor_get(v_a_992_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_a_992_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_995_ = v_a_992_;
v_isShared_996_ = v_isSharedCheck_1053_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_val_993_);
lean_dec(v_a_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1053_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v_fvarId_997_; lean_object* v_binderName_998_; lean_object* v_type_999_; lean_object* v_value_1000_; lean_object* v___x_1001_; 
v_fvarId_997_ = lean_ctor_get(v_val_993_, 0);
v_binderName_998_ = lean_ctor_get(v_val_993_, 1);
v_type_999_ = lean_ctor_get(v_val_993_, 2);
v_value_1000_ = lean_ctor_get(v_val_993_, 3);
lean_inc_ref(v_type_999_);
v___x_1001_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_999_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1051_; 
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1051_ == 0)
{
lean_object* v_unused_1052_; 
v_unused_1052_ = lean_ctor_get(v___x_1001_, 0);
lean_dec(v_unused_1052_);
v___x_1003_ = v___x_1001_;
v_isShared_1004_ = v_isSharedCheck_1051_;
goto v_resetjp_1002_;
}
else
{
lean_dec(v___x_1001_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1051_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; uint8_t v___x_1006_; 
lean_inc_ref(v_abstract_897_);
lean_inc(v_fvarId_997_);
v___x_1005_ = lean_apply_1(v_abstract_897_, v_fvarId_997_);
v___x_1006_ = lean_unbox(v___x_1005_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; 
lean_del_object(v___x_1003_);
lean_inc(v_value_1000_);
v___x_1007_ = l_Lean_Compiler_LCNF_Closure_collectLetValue(v_value_1000_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1031_; 
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1031_ == 0)
{
lean_object* v_unused_1032_; 
v_unused_1032_ = lean_ctor_get(v___x_1007_, 0);
lean_dec(v_unused_1032_);
v___x_1009_ = v___x_1007_;
v_isShared_1010_ = v_isSharedCheck_1031_;
goto v_resetjp_1008_;
}
else
{
lean_dec(v___x_1007_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1031_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v_visited_1012_; lean_object* v_params_1013_; lean_object* v_decls_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1030_; 
v___x_1011_ = lean_st_ref_take(v_a_883_);
v_visited_1012_ = lean_ctor_get(v___x_1011_, 0);
v_params_1013_ = lean_ctor_get(v___x_1011_, 1);
v_decls_1014_ = lean_ctor_get(v___x_1011_, 2);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1016_ = v___x_1011_;
v_isShared_1017_ = v_isSharedCheck_1030_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_decls_1014_);
lean_inc(v_params_1013_);
lean_inc(v_visited_1012_);
lean_dec(v___x_1011_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1030_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1018_ = lean_box(0);
if (v_isShared_996_ == 0)
{
lean_ctor_set_tag(v___x_995_, 0);
v___x_1020_ = v___x_995_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_val_993_);
v___x_1020_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1021_ = lean_array_push(v_decls_1014_, v___x_1020_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 2, v___x_1021_);
v___x_1023_ = v___x_1016_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_visited_1012_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_params_1013_);
lean_ctor_set(v_reuseFailAlloc_1028_, 2, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1024_ = lean_st_ref_put(v_a_883_, v___x_1023_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1018_);
v___x_1026_ = v___x_1009_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1018_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_995_);
lean_dec(v_val_993_);
return v___x_1007_;
}
}
else
{
lean_object* v___x_1033_; lean_object* v_visited_1034_; lean_object* v_params_1035_; lean_object* v_decls_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1050_; 
lean_inc_ref(v_type_999_);
lean_inc(v_binderName_998_);
lean_inc(v_fvarId_997_);
lean_del_object(v___x_995_);
lean_dec(v_val_993_);
v___x_1033_ = lean_st_ref_take(v_a_883_);
v_visited_1034_ = lean_ctor_get(v___x_1033_, 0);
v_params_1035_ = lean_ctor_get(v___x_1033_, 1);
v_decls_1036_ = lean_ctor_get(v___x_1033_, 2);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1038_ = v___x_1033_;
v_isShared_1039_ = v_isSharedCheck_1050_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_decls_1036_);
lean_inc(v_params_1035_);
lean_inc(v_visited_1034_);
lean_dec(v___x_1033_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1050_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1040_ = lean_box(0);
v___x_1041_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1041_, 0, v_fvarId_997_);
lean_ctor_set(v___x_1041_, 1, v_binderName_998_);
lean_ctor_set(v___x_1041_, 2, v_type_999_);
lean_ctor_set_uint8(v___x_1041_, sizeof(void*)*3, v___x_891_);
v___x_1042_ = lean_array_push(v_params_1035_, v___x_1041_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 1, v___x_1042_);
v___x_1044_ = v___x_1038_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_visited_1034_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_decls_1036_);
v___x_1044_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1045_ = lean_st_ref_put(v_a_883_, v___x_1044_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___x_1040_);
v___x_1047_ = v___x_1003_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1040_);
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
lean_del_object(v___x_995_);
lean_dec(v_val_993_);
return v___x_1001_;
}
}
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec(v_a_992_);
v___x_1054_ = lean_obj_once(&l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3, &l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3_once, _init_l_Lean_Compiler_LCNF_Closure_collectFVar___closed__3);
v___x_1055_ = l_panic___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__5(v___x_1054_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
return v___x_1055_;
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_a_1056_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_991_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_991_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec(v_fvarId_881_);
v_a_1064_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_964_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_964_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec(v_fvarId_881_);
v_a_1073_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_905_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_905_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
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
else
{
lean_dec(v_fvarId_881_);
return v___x_892_;
}
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec(v_fvarId_881_);
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType___lam__0(lean_object* v_e_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = l_Lean_Expr_fvarId_x21(v_e_1085_);
v___x_1094_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v___x_1093_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectArg___boxed(lean_object* v_arg_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_Compiler_LCNF_Closure_collectArg(v_arg_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectType___boxed(lean_object* v_type_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_Compiler_LCNF_Closure_collectType(v_type_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFunDecl___boxed(lean_object* v_decl_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_Compiler_LCNF_Closure_collectFunDecl(v_decl_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7___boxed(lean_object* v_as_1122_, lean_object* v_i_1123_, lean_object* v_stop_1124_, lean_object* v_b_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
size_t v_i_boxed_1133_; size_t v_stop_boxed_1134_; lean_object* v_res_1135_; 
v_i_boxed_1133_ = lean_unbox_usize(v_i_1123_);
lean_dec(v_i_1123_);
v_stop_boxed_1134_ = lean_unbox_usize(v_stop_1124_);
lean_dec(v_stop_1124_);
v_res_1135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectLetValue_spec__7(v_as_1122_, v_i_boxed_1133_, v_stop_boxed_1134_, v_b_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec_ref(v_as_1122_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0___boxed(lean_object* v_as_1136_, lean_object* v_i_1137_, lean_object* v_stop_1138_, lean_object* v_b_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
size_t v_i_boxed_1147_; size_t v_stop_boxed_1148_; lean_object* v_res_1149_; 
v_i_boxed_1147_ = lean_unbox_usize(v_i_1137_);
lean_dec(v_i_1137_);
v_stop_boxed_1148_ = lean_unbox_usize(v_stop_1138_);
lean_dec(v_stop_1138_);
v_res_1149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectParams_spec__0(v_as_1136_, v_i_boxed_1147_, v_stop_boxed_1148_, v_b_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec_ref(v_as_1136_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectParams___boxed(lean_object* v_params_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_Compiler_LCNF_Closure_collectParams(v_params_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec_ref(v_params_1150_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11___boxed(lean_object* v_as_1159_, lean_object* v_i_1160_, lean_object* v_stop_1161_, lean_object* v_b_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
size_t v_i_boxed_1170_; size_t v_stop_boxed_1171_; lean_object* v_res_1172_; 
v_i_boxed_1170_ = lean_unbox_usize(v_i_1160_);
lean_dec(v_i_1160_);
v_stop_boxed_1171_ = lean_unbox_usize(v_stop_1161_);
lean_dec(v_stop_1161_);
v_res_1172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_collectCode_spec__11(v_as_1159_, v_i_boxed_1170_, v_stop_boxed_1171_, v_b_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectLetValue___boxed(lean_object* v_e_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_Compiler_LCNF_Closure_collectLetValue(v_e_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectCode___boxed(lean_object* v_c_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_Compiler_LCNF_Closure_collectCode(v_c_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_collectFVar___boxed(lean_object* v_fvarId_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_Compiler_LCNF_Closure_collectFVar(v_fvarId_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
return v_res_1199_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4(lean_object* v_00_u03b2_1200_, lean_object* v_m_1201_, lean_object* v_a_1202_){
_start:
{
uint8_t v___x_1203_; 
v___x_1203_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___redArg(v_m_1201_, v_a_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4___boxed(lean_object* v_00_u03b2_1204_, lean_object* v_m_1205_, lean_object* v_a_1206_){
_start:
{
uint8_t v_res_1207_; lean_object* v_r_1208_; 
v_res_1207_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Closure_collectFVar_spec__4(v_00_u03b2_1204_, v_m_1205_, v_a_1206_);
lean_dec(v_a_1206_);
lean_dec_ref(v_m_1205_);
v_r_1208_ = lean_box(v_res_1207_);
return v_r_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9(lean_object* v_e_1209_, lean_object* v_a_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___redArg(v_e_1209_, v_a_1210_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9___boxed(lean_object* v_e_1219_, lean_object* v_a_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__9(v_e_1219_, v_a_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v_a_1220_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10(lean_object* v_e_1229_, lean_object* v_a_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___redArg(v_e_1229_, v_a_1230_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10___boxed(lean_object* v_e_1239_, lean_object* v_a_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10(v_e_1239_, v_a_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v_a_1240_);
return v_res_1248_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14(lean_object* v_00_u03b2_1249_, lean_object* v_m_1250_, lean_object* v_a_1251_){
_start:
{
uint8_t v___x_1252_; 
v___x_1252_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___redArg(v_m_1250_, v_a_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14___boxed(lean_object* v_00_u03b2_1253_, lean_object* v_m_1254_, lean_object* v_a_1255_){
_start:
{
uint8_t v_res_1256_; lean_object* v_r_1257_; 
v_res_1256_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14(v_00_u03b2_1253_, v_m_1254_, v_a_1255_);
lean_dec_ref(v_a_1255_);
lean_dec_ref(v_m_1254_);
v_r_1257_ = lean_box(v_res_1256_);
return v_r_1257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15(lean_object* v_00_u03b2_1258_, lean_object* v_m_1259_, lean_object* v_a_1260_, lean_object* v_b_1261_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15___redArg(v_m_1259_, v_a_1260_, v_b_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15(lean_object* v_00_u03b2_1263_, lean_object* v_a_1264_, lean_object* v_x_1265_){
_start:
{
uint8_t v___x_1266_; 
v___x_1266_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___redArg(v_a_1264_, v_x_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15___boxed(lean_object* v_00_u03b2_1267_, lean_object* v_a_1268_, lean_object* v_x_1269_){
_start:
{
uint8_t v_res_1270_; lean_object* v_r_1271_; 
v_res_1270_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__14_spec__15(v_00_u03b2_1267_, v_a_1268_, v_x_1269_);
lean_dec(v_x_1269_);
lean_dec_ref(v_a_1268_);
v_r_1271_ = lean_box(v_res_1270_);
return v_r_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17(lean_object* v_00_u03b2_1272_, lean_object* v_data_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17___redArg(v_data_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18(lean_object* v_00_u03b2_1275_, lean_object* v_i_1276_, lean_object* v_source_1277_, lean_object* v_target_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18___redArg(v_i_1276_, v_source_1277_, v_target_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_1280_, lean_object* v_x_1281_, lean_object* v_x_1282_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_Compiler_LCNF_Closure_collectType_spec__2_spec__4_spec__10_spec__15_spec__17_spec__18_spec__19___redArg(v_x_1281_, v_x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(lean_object* v_k_1284_, lean_object* v_t_1285_){
_start:
{
if (lean_obj_tag(v_t_1285_) == 0)
{
lean_object* v_k_1286_; lean_object* v_l_1287_; lean_object* v_r_1288_; uint8_t v___x_1289_; 
v_k_1286_ = lean_ctor_get(v_t_1285_, 1);
v_l_1287_ = lean_ctor_get(v_t_1285_, 3);
v_r_1288_ = lean_ctor_get(v_t_1285_, 4);
v___x_1289_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1284_, v_k_1286_);
switch(v___x_1289_)
{
case 0:
{
v_t_1285_ = v_l_1287_;
goto _start;
}
case 1:
{
uint8_t v___x_1291_; 
v___x_1291_ = 1;
return v___x_1291_;
}
default: 
{
v_t_1285_ = v_r_1288_;
goto _start;
}
}
}
else
{
uint8_t v___x_1293_; 
v___x_1293_ = 0;
return v___x_1293_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg___boxed(lean_object* v_k_1294_, lean_object* v_t_1295_){
_start:
{
uint8_t v_res_1296_; lean_object* v_r_1297_; 
v_res_1296_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(v_k_1294_, v_t_1295_);
lean_dec(v_t_1295_);
lean_dec(v_k_1294_);
v_r_1297_ = lean_box(v_res_1296_);
return v_r_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(lean_object* v_a_1298_, lean_object* v_as_1299_, size_t v_i_1300_, size_t v_stop_1301_, lean_object* v_b_1302_){
_start:
{
lean_object* v___y_1304_; uint8_t v___x_1308_; 
v___x_1308_ = lean_usize_dec_eq(v_i_1300_, v_stop_1301_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1309_ = lean_array_uget_borrowed(v_as_1299_, v_i_1300_);
v___x_1310_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v___x_1309_);
v___x_1311_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(v___x_1310_, v_a_1298_);
lean_dec(v___x_1310_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; 
lean_inc(v___x_1309_);
v___x_1312_ = lean_array_push(v_b_1302_, v___x_1309_);
v___y_1304_ = v___x_1312_;
goto v___jp_1303_;
}
else
{
v___y_1304_ = v_b_1302_;
goto v___jp_1303_;
}
}
else
{
return v_b_1302_;
}
v___jp_1303_:
{
size_t v___x_1305_; size_t v___x_1306_; 
v___x_1305_ = ((size_t)1ULL);
v___x_1306_ = lean_usize_add(v_i_1300_, v___x_1305_);
v_i_1300_ = v___x_1306_;
v_b_1302_ = v___y_1304_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2___boxed(lean_object* v_a_1313_, lean_object* v_as_1314_, lean_object* v_i_1315_, lean_object* v_stop_1316_, lean_object* v_b_1317_){
_start:
{
size_t v_i_boxed_1318_; size_t v_stop_boxed_1319_; lean_object* v_res_1320_; 
v_i_boxed_1318_ = lean_unbox_usize(v_i_1315_);
lean_dec(v_i_1315_);
v_stop_boxed_1319_ = lean_unbox_usize(v_stop_1316_);
lean_dec(v_stop_1316_);
v_res_1320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(v_a_1313_, v_as_1314_, v_i_boxed_1318_, v_stop_boxed_1319_, v_b_1317_);
lean_dec_ref(v_as_1314_);
lean_dec(v_a_1313_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(lean_object* v_as_1321_, size_t v_sz_1322_, size_t v_i_1323_, lean_object* v_b_1324_){
_start:
{
uint8_t v___x_1326_; 
v___x_1326_ = lean_usize_dec_lt(v_i_1323_, v_sz_1322_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1327_, 0, v_b_1324_);
return v___x_1327_;
}
else
{
lean_object* v_a_1328_; lean_object* v_fvarId_1329_; lean_object* v___x_1330_; size_t v___x_1331_; size_t v___x_1332_; 
v_a_1328_ = lean_array_uget_borrowed(v_as_1321_, v_i_1323_);
v_fvarId_1329_ = lean_ctor_get(v_a_1328_, 0);
lean_inc(v_fvarId_1329_);
v___x_1330_ = l_Lean_FVarIdSet_insert(v_b_1324_, v_fvarId_1329_);
v___x_1331_ = ((size_t)1ULL);
v___x_1332_ = lean_usize_add(v_i_1323_, v___x_1331_);
v_i_1323_ = v___x_1332_;
v_b_1324_ = v___x_1330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg___boxed(lean_object* v_as_1334_, lean_object* v_sz_1335_, lean_object* v_i_1336_, lean_object* v_b_1337_, lean_object* v___y_1338_){
_start:
{
size_t v_sz_boxed_1339_; size_t v_i_boxed_1340_; lean_object* v_res_1341_; 
v_sz_boxed_1339_ = lean_unbox_usize(v_sz_1335_);
lean_dec(v_sz_1335_);
v_i_boxed_1340_ = lean_unbox_usize(v_i_1336_);
lean_dec(v_i_1336_);
v_res_1341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(v_as_1334_, v_sz_boxed_1339_, v_i_boxed_1340_, v_b_1337_);
lean_dec_ref(v_as_1334_);
return v_res_1341_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = ((lean_object*)(l_Lean_Compiler_LCNF_Closure_run___redArg___closed__0));
v___x_1345_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_1346_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v___x_1344_);
lean_ctor_set(v___x_1346_, 2, v___x_1344_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run___redArg(lean_object* v_x_1347_, lean_object* v_inScope_1348_, lean_object* v_abstract_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1355_ = lean_box(1);
v___x_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1356_, 0, v_inScope_1348_);
lean_ctor_set(v___x_1356_, 1, v_abstract_1349_);
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = ((lean_object*)(l_Lean_Compiler_LCNF_Closure_run___redArg___closed__0));
v___x_1359_ = lean_obj_once(&l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1, &l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Closure_run___redArg___closed__1);
v___x_1360_ = lean_st_mk_ref(v___x_1359_);
lean_inc(v_a_1353_);
lean_inc_ref(v_a_1352_);
lean_inc(v_a_1351_);
lean_inc_ref(v_a_1350_);
lean_inc(v___x_1360_);
v___x_1361_ = lean_apply_7(v_x_1347_, v___x_1356_, v___x_1360_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, lean_box(0));
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1363_; lean_object* v_params_1364_; lean_object* v_decls_1365_; size_t v_sz_1366_; size_t v___x_1367_; lean_object* v___x_1368_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref_known(v___x_1361_, 1);
v___x_1363_ = lean_st_ref_get(v___x_1360_);
lean_dec(v___x_1360_);
v_params_1364_ = lean_ctor_get(v___x_1363_, 1);
lean_inc_ref(v_params_1364_);
v_decls_1365_ = lean_ctor_get(v___x_1363_, 2);
lean_inc_ref(v_decls_1365_);
lean_dec(v___x_1363_);
v_sz_1366_ = lean_array_size(v_params_1364_);
v___x_1367_ = ((size_t)0ULL);
v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(v_params_1364_, v_sz_1366_, v___x_1367_, v___x_1355_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1387_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1387_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1387_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___y_1374_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1380_ = lean_array_get_size(v_decls_1365_);
v___x_1381_ = lean_nat_dec_lt(v___x_1357_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_dec(v_a_1369_);
lean_dec_ref(v_decls_1365_);
v___y_1374_ = v___x_1358_;
goto v___jp_1373_;
}
else
{
uint8_t v___x_1382_; 
v___x_1382_ = lean_nat_dec_le(v___x_1380_, v___x_1380_);
if (v___x_1382_ == 0)
{
if (v___x_1381_ == 0)
{
lean_dec(v_a_1369_);
lean_dec_ref(v_decls_1365_);
v___y_1374_ = v___x_1358_;
goto v___jp_1373_;
}
else
{
size_t v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = lean_usize_of_nat(v___x_1380_);
v___x_1384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(v_a_1369_, v_decls_1365_, v___x_1367_, v___x_1383_, v___x_1358_);
lean_dec_ref(v_decls_1365_);
lean_dec(v_a_1369_);
v___y_1374_ = v___x_1384_;
goto v___jp_1373_;
}
}
else
{
size_t v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_usize_of_nat(v___x_1380_);
v___x_1386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Closure_run_spec__2(v_a_1369_, v_decls_1365_, v___x_1367_, v___x_1385_, v___x_1358_);
lean_dec_ref(v_decls_1365_);
lean_dec(v_a_1369_);
v___y_1374_ = v___x_1386_;
goto v___jp_1373_;
}
}
v___jp_1373_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v_params_1364_);
lean_ctor_set(v___x_1375_, 1, v___y_1374_);
v___x_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1376_, 0, v_a_1362_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1376_);
v___x_1378_ = v___x_1371_;
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
return v___x_1378_;
}
}
}
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_dec_ref(v_decls_1365_);
lean_dec_ref(v_params_1364_);
lean_dec(v_a_1362_);
v_a_1388_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1368_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1368_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_dec(v___x_1360_);
v_a_1396_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1361_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1361_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run___redArg___boxed(lean_object* v_x_1404_, lean_object* v_inScope_1405_, lean_object* v_abstract_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_Compiler_LCNF_Closure_run___redArg(v_x_1404_, v_inScope_1405_, v_abstract_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run(lean_object* v_00_u03b1_1413_, lean_object* v_x_1414_, lean_object* v_inScope_1415_, lean_object* v_abstract_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_Compiler_LCNF_Closure_run___redArg(v_x_1414_, v_inScope_1415_, v_abstract_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Closure_run___boxed(lean_object* v_00_u03b1_1423_, lean_object* v_x_1424_, lean_object* v_inScope_1425_, lean_object* v_abstract_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_Compiler_LCNF_Closure_run(v_00_u03b1_1423_, v_x_1424_, v_inScope_1425_, v_abstract_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0(lean_object* v_as_1433_, size_t v_sz_1434_, size_t v_i_1435_, lean_object* v_b_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___redArg(v_as_1433_, v_sz_1434_, v_i_1435_, v_b_1436_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0___boxed(lean_object* v_as_1443_, lean_object* v_sz_1444_, lean_object* v_i_1445_, lean_object* v_b_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
size_t v_sz_boxed_1452_; size_t v_i_boxed_1453_; lean_object* v_res_1454_; 
v_sz_boxed_1452_ = lean_unbox_usize(v_sz_1444_);
lean_dec(v_sz_1444_);
v_i_boxed_1453_ = lean_unbox_usize(v_i_1445_);
lean_dec(v_i_1445_);
v_res_1454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Closure_run_spec__0(v_as_1443_, v_sz_boxed_1452_, v_i_boxed_1453_, v_b_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec_ref(v_as_1443_);
return v_res_1454_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1(lean_object* v_00_u03b2_1455_, lean_object* v_k_1456_, lean_object* v_t_1457_){
_start:
{
uint8_t v___x_1458_; 
v___x_1458_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___redArg(v_k_1456_, v_t_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1___boxed(lean_object* v_00_u03b2_1459_, lean_object* v_k_1460_, lean_object* v_t_1461_){
_start:
{
uint8_t v_res_1462_; lean_object* v_r_1463_; 
v_res_1462_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Closure_run_spec__1(v_00_u03b2_1459_, v_k_1460_, v_t_1461_);
lean_dec(v_t_1461_);
lean_dec(v_k_1460_);
v_r_1463_ = lean_box(v_res_1462_);
return v_r_1463_;
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
