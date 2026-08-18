// Lean compiler output
// Module: Lean.Meta.Sym.LetToHave
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.Sym.InferType import Lean.Meta.Sym.ReplaceS import Lean.Meta.Sym.AlphaShareBuilder
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
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVar_x21(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getZetaDeltaFVarIds___redArg(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_map, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_pure, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_seqRight, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_bind, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "_private.Lean.Meta.Sym.ReplaceS.0.Lean.Meta.Sym.visit"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.ReplaceS"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Sym.AlphaShareBuilder"};
static const lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.Sym.Internal.liftBuilderM"};
static const lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "`Sym.letToHave` failed, type error"};
static const lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1;
static const lean_string_object l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "\nis not definitionally equal to"};
static const lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "`Sym.letToHave` failed, function expected"};
static const lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_isClean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_isClean___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.Sym.LetToHave"};
static const lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "_private.Lean.Meta.Sym.LetToHave.0.Lean.Meta.Sym.LetToHave.inferTypeO"};
static const lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Meta.Sym.LetToHave.0.Lean.Meta.Sym.LetToHave.checkFun"};
static const lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Meta.Sym.LetToHave.0.Lean.Meta.Sym.LetToHave.checkApp"};
static const lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Meta.Sym.LetToHave.0.Lean.Meta.Sym.LetToHave.visitCore"};
static const lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_letToHave___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_letToHave___lam__3___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_letToHave___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_letToHave___lam__3___closed__1;
static lean_once_cell_t l_Lean_Meta_Sym_letToHave___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_letToHave___lam__3___closed__2;
static lean_once_cell_t l_Lean_Meta_Sym_letToHave___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_letToHave___lam__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_letToHave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "`Sym.letToHave` internal error, input term has loose bound variables"};
static const lean_object* l_Lean_Meta_Sym_letToHave___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_letToHave___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_letToHave___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_letToHave___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___lam__0(lean_object* v_a_1_, lean_object* v_visited_2_, lean_object* v_types_3_, lean_object* v_subst_4_, lean_object* v_a_x3f_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_visitedClosed_8_; lean_object* v_hasDepLetCache_9_; lean_object* v_numConverted_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_20_; 
v___x_7_ = lean_st_ref_take(v_a_1_);
v_visitedClosed_8_ = lean_ctor_get(v___x_7_, 3);
v_hasDepLetCache_9_ = lean_ctor_get(v___x_7_, 4);
v_numConverted_10_ = lean_ctor_get(v___x_7_, 5);
v_isSharedCheck_20_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_20_ == 0)
{
lean_object* v_unused_21_; lean_object* v_unused_22_; lean_object* v_unused_23_; 
v_unused_21_ = lean_ctor_get(v___x_7_, 2);
lean_dec(v_unused_21_);
v_unused_22_ = lean_ctor_get(v___x_7_, 1);
lean_dec(v_unused_22_);
v_unused_23_ = lean_ctor_get(v___x_7_, 0);
lean_dec(v_unused_23_);
v___x_12_ = v___x_7_;
v_isShared_13_ = v_isSharedCheck_20_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_numConverted_10_);
lean_inc(v_hasDepLetCache_9_);
lean_inc(v_visitedClosed_8_);
lean_dec(v___x_7_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_20_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_15_; 
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 2, v_subst_4_);
lean_ctor_set(v___x_12_, 1, v_types_3_);
lean_ctor_set(v___x_12_, 0, v_visited_2_);
v___x_15_ = v___x_12_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_19_; 
v_reuseFailAlloc_19_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_19_, 0, v_visited_2_);
lean_ctor_set(v_reuseFailAlloc_19_, 1, v_types_3_);
lean_ctor_set(v_reuseFailAlloc_19_, 2, v_subst_4_);
lean_ctor_set(v_reuseFailAlloc_19_, 3, v_visitedClosed_8_);
lean_ctor_set(v_reuseFailAlloc_19_, 4, v_hasDepLetCache_9_);
lean_ctor_set(v_reuseFailAlloc_19_, 5, v_numConverted_10_);
v___x_15_ = v_reuseFailAlloc_19_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_16_ = lean_st_ref_put(v_a_1_, v___x_15_);
v___x_17_ = lean_box(0);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___lam__0___boxed(lean_object* v_a_24_, lean_object* v_visited_25_, lean_object* v_types_26_, lean_object* v_subst_27_, lean_object* v_a_x3f_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___lam__0(v_a_24_, v_visited_25_, v_types_26_, v_subst_27_, v_a_x3f_28_);
lean_dec(v_a_x3f_28_);
lean_dec(v_a_24_);
return v_res_30_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__0(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_box(0);
v___x_32_ = lean_unsigned_to_nat(16u);
v___x_33_ = lean_mk_array(v___x_32_, v___x_31_);
return v___x_33_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__0, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__0);
v___x_35_ = lean_unsigned_to_nat(0u);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v___x_34_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg(lean_object* v_x_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v___x_47_; lean_object* v_visited_48_; lean_object* v_types_49_; lean_object* v_subst_50_; lean_object* v_visitedClosed_51_; lean_object* v_hasDepLetCache_52_; lean_object* v_numConverted_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_91_; 
v___x_47_ = lean_st_ref_take(v_a_39_);
v_visited_48_ = lean_ctor_get(v___x_47_, 0);
v_types_49_ = lean_ctor_get(v___x_47_, 1);
v_subst_50_ = lean_ctor_get(v___x_47_, 2);
v_visitedClosed_51_ = lean_ctor_get(v___x_47_, 3);
v_hasDepLetCache_52_ = lean_ctor_get(v___x_47_, 4);
v_numConverted_53_ = lean_ctor_get(v___x_47_, 5);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_91_ == 0)
{
v___x_55_ = v___x_47_;
v_isShared_56_ = v_isSharedCheck_91_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_numConverted_53_);
lean_inc(v_hasDepLetCache_52_);
lean_inc(v_visitedClosed_51_);
lean_inc(v_subst_50_);
lean_inc(v_types_49_);
lean_inc(v_visited_48_);
lean_dec(v___x_47_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_91_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_57_; lean_object* v___x_59_; 
v___x_57_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 2, v___x_57_);
lean_ctor_set(v___x_55_, 1, v___x_57_);
lean_ctor_set(v___x_55_, 0, v___x_57_);
v___x_59_ = v___x_55_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_57_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v___x_57_);
lean_ctor_set(v_reuseFailAlloc_90_, 2, v___x_57_);
lean_ctor_set(v_reuseFailAlloc_90_, 3, v_visitedClosed_51_);
lean_ctor_set(v_reuseFailAlloc_90_, 4, v_hasDepLetCache_52_);
lean_ctor_set(v_reuseFailAlloc_90_, 5, v_numConverted_53_);
v___x_59_ = v_reuseFailAlloc_90_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
lean_object* v___x_60_; lean_object* v_r_61_; 
v___x_60_ = lean_st_ref_put(v_a_39_, v___x_59_);
lean_inc(v_a_45_);
lean_inc_ref(v_a_44_);
lean_inc(v_a_43_);
lean_inc_ref(v_a_42_);
lean_inc(v_a_41_);
lean_inc_ref(v_a_40_);
lean_inc(v_a_39_);
lean_inc_ref(v_a_38_);
v_r_61_ = lean_apply_9(v_x_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, lean_box(0));
if (lean_obj_tag(v_r_61_) == 0)
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_78_; 
v_a_62_ = lean_ctor_get(v_r_61_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v_r_61_);
if (v_isSharedCheck_78_ == 0)
{
v___x_64_ = v_r_61_;
v_isShared_65_ = v_isSharedCheck_78_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v_r_61_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_78_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
lean_inc(v_a_62_);
if (v_isShared_65_ == 0)
{
lean_ctor_set_tag(v___x_64_, 1);
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_a_62_);
v___x_67_ = v_reuseFailAlloc_77_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
lean_object* v___x_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_75_; 
v___x_68_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___lam__0(v_a_39_, v_visited_48_, v_types_49_, v_subst_50_, v___x_67_);
lean_dec_ref(v___x_67_);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_75_ == 0)
{
lean_object* v_unused_76_; 
v_unused_76_ = lean_ctor_get(v___x_68_, 0);
lean_dec(v_unused_76_);
v___x_70_ = v___x_68_;
v_isShared_71_ = v_isSharedCheck_75_;
goto v_resetjp_69_;
}
else
{
lean_dec(v___x_68_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_75_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_73_; 
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v_a_62_);
v___x_73_ = v___x_70_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_a_62_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
}
else
{
lean_object* v_a_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
v_a_79_ = lean_ctor_get(v_r_61_, 0);
lean_inc(v_a_79_);
lean_dec_ref_known(v_r_61_, 1);
v___x_80_ = lean_box(0);
v___x_81_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___lam__0(v_a_39_, v_visited_48_, v_types_49_, v_subst_50_, v___x_80_);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_88_ == 0)
{
lean_object* v_unused_89_; 
v_unused_89_ = lean_ctor_get(v___x_81_, 0);
lean_dec(v_unused_89_);
v___x_83_ = v___x_81_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_dec(v___x_81_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set_tag(v___x_83_, 1);
lean_ctor_set(v___x_83_, 0, v_a_79_);
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_79_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___boxed(lean_object* v_x_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg(v_x_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope(lean_object* v_00_u03b1_103_, lean_object* v_x_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_114_; lean_object* v_visited_115_; lean_object* v_types_116_; lean_object* v_subst_117_; lean_object* v_visitedClosed_118_; lean_object* v_hasDepLetCache_119_; lean_object* v_numConverted_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_158_; 
v___x_114_ = lean_st_ref_take(v_a_106_);
v_visited_115_ = lean_ctor_get(v___x_114_, 0);
v_types_116_ = lean_ctor_get(v___x_114_, 1);
v_subst_117_ = lean_ctor_get(v___x_114_, 2);
v_visitedClosed_118_ = lean_ctor_get(v___x_114_, 3);
v_hasDepLetCache_119_ = lean_ctor_get(v___x_114_, 4);
v_numConverted_120_ = lean_ctor_get(v___x_114_, 5);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_158_ == 0)
{
v___x_122_ = v___x_114_;
v_isShared_123_ = v_isSharedCheck_158_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_numConverted_120_);
lean_inc(v_hasDepLetCache_119_);
lean_inc(v_visitedClosed_118_);
lean_inc(v_subst_117_);
lean_inc(v_types_116_);
lean_inc(v_visited_115_);
lean_dec(v___x_114_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_158_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_124_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 2, v___x_124_);
lean_ctor_set(v___x_122_, 1, v___x_124_);
lean_ctor_set(v___x_122_, 0, v___x_124_);
v___x_126_ = v___x_122_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_157_, 3, v_visitedClosed_118_);
lean_ctor_set(v_reuseFailAlloc_157_, 4, v_hasDepLetCache_119_);
lean_ctor_set(v_reuseFailAlloc_157_, 5, v_numConverted_120_);
v___x_126_ = v_reuseFailAlloc_157_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_127_; lean_object* v_r_128_; 
v___x_127_ = lean_st_ref_put(v_a_106_, v___x_126_);
lean_inc(v_a_112_);
lean_inc_ref(v_a_111_);
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
lean_inc(v_a_106_);
lean_inc_ref(v_a_105_);
v_r_128_ = lean_apply_9(v_x_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, lean_box(0));
if (lean_obj_tag(v_r_128_) == 0)
{
lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_145_; 
v_a_129_ = lean_ctor_get(v_r_128_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v_r_128_);
if (v_isSharedCheck_145_ == 0)
{
v___x_131_ = v_r_128_;
v_isShared_132_ = v_isSharedCheck_145_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v_r_128_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_145_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_134_; 
lean_inc(v_a_129_);
if (v_isShared_132_ == 0)
{
lean_ctor_set_tag(v___x_131_, 1);
v___x_134_ = v___x_131_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_129_);
v___x_134_ = v_reuseFailAlloc_144_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_142_; 
v___x_135_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___lam__0(v_a_106_, v_visited_115_, v_types_116_, v_subst_117_, v___x_134_);
lean_dec_ref(v___x_134_);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; 
v_unused_143_ = lean_ctor_get(v___x_135_, 0);
lean_dec(v_unused_143_);
v___x_137_ = v___x_135_;
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
else
{
lean_dec(v___x_135_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v_a_129_);
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_a_129_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
}
else
{
lean_object* v_a_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
v_a_146_ = lean_ctor_get(v_r_128_, 0);
lean_inc(v_a_146_);
lean_dec_ref_known(v_r_128_, 1);
v___x_147_ = lean_box(0);
v___x_148_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___lam__0(v_a_106_, v_visited_115_, v_types_116_, v_subst_117_, v___x_147_);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; 
v_unused_156_ = lean_ctor_get(v___x_148_, 0);
lean_dec(v_unused_156_);
v___x_150_ = v___x_148_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_dec(v___x_148_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set_tag(v___x_150_, 1);
lean_ctor_set(v___x_150_, 0, v_a_146_);
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_146_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___boxed(lean_object* v_00_u03b1_159_, lean_object* v_x_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope(v_00_u03b1_159_, v_x_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_171_, lean_object* v_x_172_){
_start:
{
if (lean_obj_tag(v_x_172_) == 0)
{
return v_x_171_;
}
else
{
lean_object* v_key_173_; lean_object* v_value_174_; lean_object* v_tail_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_201_; 
v_key_173_ = lean_ctor_get(v_x_172_, 0);
v_value_174_ = lean_ctor_get(v_x_172_, 1);
v_tail_175_ = lean_ctor_get(v_x_172_, 2);
v_isSharedCheck_201_ = !lean_is_exclusive(v_x_172_);
if (v_isSharedCheck_201_ == 0)
{
v___x_177_ = v_x_172_;
v_isShared_178_ = v_isSharedCheck_201_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_tail_175_);
lean_inc(v_value_174_);
lean_inc(v_key_173_);
lean_dec(v_x_172_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_201_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; size_t v___x_180_; size_t v___x_181_; size_t v___x_182_; uint64_t v___x_183_; uint64_t v___x_184_; uint64_t v___x_185_; uint64_t v_fold_186_; uint64_t v___x_187_; uint64_t v___x_188_; uint64_t v___x_189_; size_t v___x_190_; size_t v___x_191_; size_t v___x_192_; size_t v___x_193_; size_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_179_ = lean_array_get_size(v_x_171_);
v___x_180_ = lean_ptr_addr(v_key_173_);
v___x_181_ = ((size_t)3ULL);
v___x_182_ = lean_usize_shift_right(v___x_180_, v___x_181_);
v___x_183_ = lean_usize_to_uint64(v___x_182_);
v___x_184_ = 32ULL;
v___x_185_ = lean_uint64_shift_right(v___x_183_, v___x_184_);
v_fold_186_ = lean_uint64_xor(v___x_183_, v___x_185_);
v___x_187_ = 16ULL;
v___x_188_ = lean_uint64_shift_right(v_fold_186_, v___x_187_);
v___x_189_ = lean_uint64_xor(v_fold_186_, v___x_188_);
v___x_190_ = lean_uint64_to_usize(v___x_189_);
v___x_191_ = lean_usize_of_nat(v___x_179_);
v___x_192_ = ((size_t)1ULL);
v___x_193_ = lean_usize_sub(v___x_191_, v___x_192_);
v___x_194_ = lean_usize_land(v___x_190_, v___x_193_);
v___x_195_ = lean_array_uget_borrowed(v_x_171_, v___x_194_);
lean_inc(v___x_195_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 2, v___x_195_);
v___x_197_ = v___x_177_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_key_173_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_value_174_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v___x_195_);
v___x_197_ = v_reuseFailAlloc_200_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; 
v___x_198_ = lean_array_uset(v_x_171_, v___x_194_, v___x_197_);
v_x_171_ = v___x_198_;
v_x_172_ = v_tail_175_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4___redArg(lean_object* v_i_202_, lean_object* v_source_203_, lean_object* v_target_204_){
_start:
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = lean_array_get_size(v_source_203_);
v___x_206_ = lean_nat_dec_lt(v_i_202_, v___x_205_);
if (v___x_206_ == 0)
{
lean_dec_ref(v_source_203_);
lean_dec(v_i_202_);
return v_target_204_;
}
else
{
lean_object* v_es_207_; lean_object* v___x_208_; lean_object* v_source_209_; lean_object* v_target_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_es_207_ = lean_array_fget(v_source_203_, v_i_202_);
v___x_208_ = lean_box(0);
v_source_209_ = lean_array_fset(v_source_203_, v_i_202_, v___x_208_);
v_target_210_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4_spec__5___redArg(v_target_204_, v_es_207_);
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_add(v_i_202_, v___x_211_);
lean_dec(v_i_202_);
v_i_202_ = v___x_212_;
v_source_203_ = v_source_209_;
v_target_204_ = v_target_210_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3___redArg(lean_object* v_data_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v_nbuckets_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_215_ = lean_array_get_size(v_data_214_);
v___x_216_ = lean_unsigned_to_nat(2u);
v_nbuckets_217_ = lean_nat_mul(v___x_215_, v___x_216_);
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_box(0);
v___x_220_ = lean_mk_array(v_nbuckets_217_, v___x_219_);
v___x_221_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4___redArg(v___x_218_, v_data_214_, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__4___redArg(lean_object* v_a_222_, lean_object* v_b_223_, lean_object* v_x_224_){
_start:
{
if (lean_obj_tag(v_x_224_) == 0)
{
lean_dec(v_b_223_);
lean_dec_ref(v_a_222_);
return v_x_224_;
}
else
{
lean_object* v_key_225_; lean_object* v_value_226_; lean_object* v_tail_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_241_; 
v_key_225_ = lean_ctor_get(v_x_224_, 0);
v_value_226_ = lean_ctor_get(v_x_224_, 1);
v_tail_227_ = lean_ctor_get(v_x_224_, 2);
v_isSharedCheck_241_ = !lean_is_exclusive(v_x_224_);
if (v_isSharedCheck_241_ == 0)
{
v___x_229_ = v_x_224_;
v_isShared_230_ = v_isSharedCheck_241_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_tail_227_);
lean_inc(v_value_226_);
lean_inc(v_key_225_);
lean_dec(v_x_224_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_241_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
size_t v___x_231_; size_t v___x_232_; uint8_t v___x_233_; 
v___x_231_ = lean_ptr_addr(v_key_225_);
v___x_232_ = lean_ptr_addr(v_a_222_);
v___x_233_ = lean_usize_dec_eq(v___x_231_, v___x_232_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__4___redArg(v_a_222_, v_b_223_, v_tail_227_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 2, v___x_234_);
v___x_236_ = v___x_229_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_key_225_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_value_226_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
else
{
lean_object* v___x_239_; 
lean_dec(v_value_226_);
lean_dec(v_key_225_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 1, v_b_223_);
lean_ctor_set(v___x_229_, 0, v_a_222_);
v___x_239_ = v___x_229_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_222_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_b_223_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_tail_227_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___redArg(lean_object* v_a_242_, lean_object* v_x_243_){
_start:
{
if (lean_obj_tag(v_x_243_) == 0)
{
uint8_t v___x_244_; 
v___x_244_ = 0;
return v___x_244_;
}
else
{
lean_object* v_key_245_; lean_object* v_tail_246_; size_t v___x_247_; size_t v___x_248_; uint8_t v___x_249_; 
v_key_245_ = lean_ctor_get(v_x_243_, 0);
v_tail_246_ = lean_ctor_get(v_x_243_, 2);
v___x_247_ = lean_ptr_addr(v_key_245_);
v___x_248_ = lean_ptr_addr(v_a_242_);
v___x_249_ = lean_usize_dec_eq(v___x_247_, v___x_248_);
if (v___x_249_ == 0)
{
v_x_243_ = v_tail_246_;
goto _start;
}
else
{
return v___x_249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___redArg___boxed(lean_object* v_a_251_, lean_object* v_x_252_){
_start:
{
uint8_t v_res_253_; lean_object* v_r_254_; 
v_res_253_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___redArg(v_a_251_, v_x_252_);
lean_dec(v_x_252_);
lean_dec_ref(v_a_251_);
v_r_254_ = lean_box(v_res_253_);
return v_r_254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(lean_object* v_m_255_, lean_object* v_a_256_, lean_object* v_b_257_){
_start:
{
lean_object* v_size_258_; lean_object* v_buckets_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_305_; 
v_size_258_ = lean_ctor_get(v_m_255_, 0);
v_buckets_259_ = lean_ctor_get(v_m_255_, 1);
v_isSharedCheck_305_ = !lean_is_exclusive(v_m_255_);
if (v_isSharedCheck_305_ == 0)
{
v___x_261_ = v_m_255_;
v_isShared_262_ = v_isSharedCheck_305_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_buckets_259_);
lean_inc(v_size_258_);
lean_dec(v_m_255_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_305_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; size_t v___x_264_; size_t v___x_265_; size_t v___x_266_; uint64_t v___x_267_; uint64_t v___x_268_; uint64_t v___x_269_; uint64_t v_fold_270_; uint64_t v___x_271_; uint64_t v___x_272_; uint64_t v___x_273_; size_t v___x_274_; size_t v___x_275_; size_t v___x_276_; size_t v___x_277_; size_t v___x_278_; lean_object* v_bkt_279_; uint8_t v___x_280_; 
v___x_263_ = lean_array_get_size(v_buckets_259_);
v___x_264_ = lean_ptr_addr(v_a_256_);
v___x_265_ = ((size_t)3ULL);
v___x_266_ = lean_usize_shift_right(v___x_264_, v___x_265_);
v___x_267_ = lean_usize_to_uint64(v___x_266_);
v___x_268_ = 32ULL;
v___x_269_ = lean_uint64_shift_right(v___x_267_, v___x_268_);
v_fold_270_ = lean_uint64_xor(v___x_267_, v___x_269_);
v___x_271_ = 16ULL;
v___x_272_ = lean_uint64_shift_right(v_fold_270_, v___x_271_);
v___x_273_ = lean_uint64_xor(v_fold_270_, v___x_272_);
v___x_274_ = lean_uint64_to_usize(v___x_273_);
v___x_275_ = lean_usize_of_nat(v___x_263_);
v___x_276_ = ((size_t)1ULL);
v___x_277_ = lean_usize_sub(v___x_275_, v___x_276_);
v___x_278_ = lean_usize_land(v___x_274_, v___x_277_);
v_bkt_279_ = lean_array_uget_borrowed(v_buckets_259_, v___x_278_);
v___x_280_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___redArg(v_a_256_, v_bkt_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v_size_x27_282_; lean_object* v___x_283_; lean_object* v_buckets_x27_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_281_ = lean_unsigned_to_nat(1u);
v_size_x27_282_ = lean_nat_add(v_size_258_, v___x_281_);
lean_dec(v_size_258_);
lean_inc(v_bkt_279_);
v___x_283_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_283_, 0, v_a_256_);
lean_ctor_set(v___x_283_, 1, v_b_257_);
lean_ctor_set(v___x_283_, 2, v_bkt_279_);
v_buckets_x27_284_ = lean_array_uset(v_buckets_259_, v___x_278_, v___x_283_);
v___x_285_ = lean_unsigned_to_nat(4u);
v___x_286_ = lean_nat_mul(v_size_x27_282_, v___x_285_);
v___x_287_ = lean_unsigned_to_nat(3u);
v___x_288_ = lean_nat_div(v___x_286_, v___x_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_array_get_size(v_buckets_x27_284_);
v___x_290_ = lean_nat_dec_le(v___x_288_, v___x_289_);
lean_dec(v___x_288_);
if (v___x_290_ == 0)
{
lean_object* v_val_291_; lean_object* v___x_293_; 
v_val_291_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3___redArg(v_buckets_x27_284_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v_val_291_);
lean_ctor_set(v___x_261_, 0, v_size_x27_282_);
v___x_293_ = v___x_261_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_size_x27_282_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_val_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
else
{
lean_object* v___x_296_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v_buckets_x27_284_);
lean_ctor_set(v___x_261_, 0, v_size_x27_282_);
v___x_296_ = v___x_261_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_size_x27_282_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_buckets_x27_284_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
else
{
lean_object* v___x_298_; lean_object* v_buckets_x27_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
lean_inc(v_bkt_279_);
v___x_298_ = lean_box(0);
v_buckets_x27_299_ = lean_array_uset(v_buckets_259_, v___x_278_, v___x_298_);
v___x_300_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__4___redArg(v_a_256_, v_b_257_, v_bkt_279_);
v___x_301_ = lean_array_uset(v_buckets_x27_299_, v___x_278_, v___x_300_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v___x_301_);
v___x_303_ = v___x_261_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_size_258_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___redArg(lean_object* v_a_306_, lean_object* v_x_307_){
_start:
{
if (lean_obj_tag(v_x_307_) == 0)
{
lean_object* v___x_308_; 
v___x_308_ = lean_box(0);
return v___x_308_;
}
else
{
lean_object* v_key_309_; lean_object* v_value_310_; lean_object* v_tail_311_; size_t v___x_312_; size_t v___x_313_; uint8_t v___x_314_; 
v_key_309_ = lean_ctor_get(v_x_307_, 0);
v_value_310_ = lean_ctor_get(v_x_307_, 1);
v_tail_311_ = lean_ctor_get(v_x_307_, 2);
v___x_312_ = lean_ptr_addr(v_key_309_);
v___x_313_ = lean_ptr_addr(v_a_306_);
v___x_314_ = lean_usize_dec_eq(v___x_312_, v___x_313_);
if (v___x_314_ == 0)
{
v_x_307_ = v_tail_311_;
goto _start;
}
else
{
lean_object* v___x_316_; 
lean_inc(v_value_310_);
v___x_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_316_, 0, v_value_310_);
return v___x_316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___redArg___boxed(lean_object* v_a_317_, lean_object* v_x_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___redArg(v_a_317_, v_x_318_);
lean_dec(v_x_318_);
lean_dec_ref(v_a_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(lean_object* v_m_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_buckets_322_; lean_object* v___x_323_; size_t v___x_324_; size_t v___x_325_; size_t v___x_326_; uint64_t v___x_327_; uint64_t v___x_328_; uint64_t v___x_329_; uint64_t v_fold_330_; uint64_t v___x_331_; uint64_t v___x_332_; uint64_t v___x_333_; size_t v___x_334_; size_t v___x_335_; size_t v___x_336_; size_t v___x_337_; size_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_buckets_322_ = lean_ctor_get(v_m_320_, 1);
v___x_323_ = lean_array_get_size(v_buckets_322_);
v___x_324_ = lean_ptr_addr(v_a_321_);
v___x_325_ = ((size_t)3ULL);
v___x_326_ = lean_usize_shift_right(v___x_324_, v___x_325_);
v___x_327_ = lean_usize_to_uint64(v___x_326_);
v___x_328_ = 32ULL;
v___x_329_ = lean_uint64_shift_right(v___x_327_, v___x_328_);
v_fold_330_ = lean_uint64_xor(v___x_327_, v___x_329_);
v___x_331_ = 16ULL;
v___x_332_ = lean_uint64_shift_right(v_fold_330_, v___x_331_);
v___x_333_ = lean_uint64_xor(v_fold_330_, v___x_332_);
v___x_334_ = lean_uint64_to_usize(v___x_333_);
v___x_335_ = lean_usize_of_nat(v___x_323_);
v___x_336_ = ((size_t)1ULL);
v___x_337_ = lean_usize_sub(v___x_335_, v___x_336_);
v___x_338_ = lean_usize_land(v___x_334_, v___x_337_);
v___x_339_ = lean_array_uget_borrowed(v_buckets_322_, v___x_338_);
v___x_340_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___redArg(v_a_321_, v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg___boxed(lean_object* v_m_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_m_341_, v_a_342_);
lean_dec_ref(v_a_342_);
lean_dec_ref(v_m_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(lean_object* v_e_344_, lean_object* v_k_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v___x_355_; lean_object* v_hasDepLetCache_356_; lean_object* v___x_357_; 
v___x_355_ = lean_st_ref_get(v_a_347_);
v_hasDepLetCache_356_ = lean_ctor_get(v___x_355_, 4);
lean_inc_ref(v_hasDepLetCache_356_);
lean_dec(v___x_355_);
v___x_357_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_hasDepLetCache_356_, v_e_344_);
lean_dec_ref(v_hasDepLetCache_356_);
if (lean_obj_tag(v___x_357_) == 1)
{
lean_object* v_val_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec_ref(v_k_345_);
lean_dec_ref(v_e_344_);
v_val_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_val_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
lean_ctor_set_tag(v___x_360_, 0);
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_val_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
else
{
lean_object* v___x_366_; 
lean_dec(v___x_357_);
lean_inc(v_a_353_);
lean_inc_ref(v_a_352_);
lean_inc(v_a_351_);
lean_inc_ref(v_a_350_);
lean_inc(v_a_349_);
lean_inc_ref(v_a_348_);
lean_inc(v_a_347_);
lean_inc_ref(v_a_346_);
v___x_366_ = lean_apply_9(v_k_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, lean_box(0));
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_390_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_390_ == 0)
{
v___x_369_ = v___x_366_;
v_isShared_370_ = v_isSharedCheck_390_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_366_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_390_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v_visited_372_; lean_object* v_types_373_; lean_object* v_subst_374_; lean_object* v_visitedClosed_375_; lean_object* v_hasDepLetCache_376_; lean_object* v_numConverted_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_389_; 
v___x_371_ = lean_st_ref_take(v_a_347_);
v_visited_372_ = lean_ctor_get(v___x_371_, 0);
v_types_373_ = lean_ctor_get(v___x_371_, 1);
v_subst_374_ = lean_ctor_get(v___x_371_, 2);
v_visitedClosed_375_ = lean_ctor_get(v___x_371_, 3);
v_hasDepLetCache_376_ = lean_ctor_get(v___x_371_, 4);
v_numConverted_377_ = lean_ctor_get(v___x_371_, 5);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_389_ == 0)
{
v___x_379_ = v___x_371_;
v_isShared_380_ = v_isSharedCheck_389_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_numConverted_377_);
lean_inc(v_hasDepLetCache_376_);
lean_inc(v_visitedClosed_375_);
lean_inc(v_subst_374_);
lean_inc(v_types_373_);
lean_inc(v_visited_372_);
lean_dec(v___x_371_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_389_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_383_; 
lean_inc(v_a_367_);
v___x_381_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_hasDepLetCache_376_, v_e_344_, v_a_367_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 4, v___x_381_);
v___x_383_ = v___x_379_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_visited_372_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_types_373_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v_subst_374_);
lean_ctor_set(v_reuseFailAlloc_388_, 3, v_visitedClosed_375_);
lean_ctor_set(v_reuseFailAlloc_388_, 4, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_388_, 5, v_numConverted_377_);
v___x_383_ = v_reuseFailAlloc_388_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_384_ = lean_st_ref_put(v_a_347_, v___x_383_);
if (v_isShared_370_ == 0)
{
v___x_386_ = v___x_369_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_367_);
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
}
else
{
lean_dec_ref(v_e_344_);
return v___x_366_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached___boxed(lean_object* v_e_391_, lean_object* v_k_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(v_e_391_, v_k_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0(lean_object* v_00_u03b2_403_, lean_object* v_m_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_m_404_, v_a_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___boxed(lean_object* v_00_u03b2_407_, lean_object* v_m_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0(v_00_u03b2_407_, v_m_408_, v_a_409_);
lean_dec_ref(v_a_409_);
lean_dec_ref(v_m_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1(lean_object* v_00_u03b2_411_, lean_object* v_m_412_, lean_object* v_a_413_, lean_object* v_b_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_m_412_, v_a_413_, v_b_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0(lean_object* v_00_u03b2_416_, lean_object* v_a_417_, lean_object* v_x_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___redArg(v_a_417_, v_x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_420_, lean_object* v_a_421_, lean_object* v_x_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0(v_00_u03b2_420_, v_a_421_, v_x_422_);
lean_dec(v_x_422_);
lean_dec_ref(v_a_421_);
return v_res_423_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2(lean_object* v_00_u03b2_424_, lean_object* v_a_425_, lean_object* v_x_426_){
_start:
{
uint8_t v___x_427_; 
v___x_427_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___redArg(v_a_425_, v_x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___boxed(lean_object* v_00_u03b2_428_, lean_object* v_a_429_, lean_object* v_x_430_){
_start:
{
uint8_t v_res_431_; lean_object* v_r_432_; 
v_res_431_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2(v_00_u03b2_428_, v_a_429_, v_x_430_);
lean_dec(v_x_430_);
lean_dec_ref(v_a_429_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3(lean_object* v_00_u03b2_433_, lean_object* v_data_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3___redArg(v_data_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__4(lean_object* v_00_u03b2_436_, lean_object* v_a_437_, lean_object* v_b_438_, lean_object* v_x_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__4___redArg(v_a_437_, v_b_438_, v_x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_441_, lean_object* v_i_442_, lean_object* v_source_443_, lean_object* v_target_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4___redArg(v_i_442_, v_source_443_, v_target_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_446_, lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4_spec__5___redArg(v_x_447_, v_x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__0___boxed(lean_object* v_t_450_, lean_object* v_b_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__0(v_t_450_, v_b_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__1(lean_object* v_type_462_, lean_object* v_value_463_, lean_object* v_body_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_type_462_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; uint8_t v___x_476_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_a_475_);
v___x_476_ = lean_unbox(v_a_475_);
lean_dec(v_a_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; 
lean_dec_ref_known(v___x_474_, 1);
v___x_477_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_value_463_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; uint8_t v___x_479_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_478_);
v___x_479_ = lean_unbox(v_a_478_);
lean_dec(v_a_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
lean_dec_ref_known(v___x_477_, 1);
v___x_480_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_body_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
return v___x_480_;
}
else
{
lean_dec_ref(v_body_464_);
return v___x_477_;
}
}
else
{
lean_dec_ref(v_body_464_);
return v___x_477_;
}
}
else
{
lean_dec_ref(v_body_464_);
lean_dec_ref(v_value_463_);
return v___x_474_;
}
}
else
{
lean_dec_ref(v_body_464_);
lean_dec_ref(v_value_463_);
return v___x_474_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__1___boxed(lean_object* v_type_481_, lean_object* v_value_482_, lean_object* v_body_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__1(v_type_481_, v_value_482_, v_body_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__2(lean_object* v_fn_494_, lean_object* v_arg_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_fn_494_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; uint8_t v___x_507_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
v___x_507_ = lean_unbox(v_a_506_);
lean_dec(v_a_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
lean_dec_ref_known(v___x_505_, 1);
v___x_508_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_arg_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
return v___x_508_;
}
else
{
lean_dec_ref(v_arg_495_);
return v___x_505_;
}
}
else
{
lean_dec_ref(v_arg_495_);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__2___boxed(lean_object* v_fn_509_, lean_object* v_arg_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__2(v_fn_509_, v_arg_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___boxed(lean_object* v_e_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_e_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_);
lean_dec(v_a_529_);
lean_dec_ref(v_a_528_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(lean_object* v_e_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_t_543_; lean_object* v_b_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; 
switch(lean_obj_tag(v_e_532_))
{
case 8:
{
uint8_t v_nondep_555_; 
v_nondep_555_ = lean_ctor_get_uint8(v_e_532_, sizeof(void*)*4 + 8);
if (v_nondep_555_ == 0)
{
uint8_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec_ref_known(v_e_532_, 4);
v___x_556_ = 1;
v___x_557_ = lean_box(v___x_556_);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
else
{
lean_object* v_type_559_; lean_object* v_value_560_; lean_object* v_body_561_; lean_object* v___f_562_; lean_object* v___x_563_; 
v_type_559_ = lean_ctor_get(v_e_532_, 1);
v_value_560_ = lean_ctor_get(v_e_532_, 2);
v_body_561_ = lean_ctor_get(v_e_532_, 3);
lean_inc_ref(v_body_561_);
lean_inc_ref(v_value_560_);
lean_inc_ref(v_type_559_);
v___f_562_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__1___boxed), 12, 3);
lean_closure_set(v___f_562_, 0, v_type_559_);
lean_closure_set(v___f_562_, 1, v_value_560_);
lean_closure_set(v___f_562_, 2, v_body_561_);
v___x_563_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(v_e_532_, v___f_562_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
return v___x_563_;
}
}
case 5:
{
lean_object* v_fn_564_; lean_object* v_arg_565_; lean_object* v___f_566_; lean_object* v___x_567_; 
v_fn_564_ = lean_ctor_get(v_e_532_, 0);
v_arg_565_ = lean_ctor_get(v_e_532_, 1);
lean_inc_ref(v_arg_565_);
lean_inc_ref(v_fn_564_);
v___f_566_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__2___boxed), 11, 2);
lean_closure_set(v___f_566_, 0, v_fn_564_);
lean_closure_set(v___f_566_, 1, v_arg_565_);
v___x_567_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(v_e_532_, v___f_566_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
return v___x_567_;
}
case 6:
{
lean_object* v_binderType_568_; lean_object* v_body_569_; 
v_binderType_568_ = lean_ctor_get(v_e_532_, 1);
v_body_569_ = lean_ctor_get(v_e_532_, 2);
lean_inc_ref(v_body_569_);
lean_inc_ref(v_binderType_568_);
v_t_543_ = v_binderType_568_;
v_b_544_ = v_body_569_;
v___y_545_ = v_a_533_;
v___y_546_ = v_a_534_;
v___y_547_ = v_a_535_;
v___y_548_ = v_a_536_;
v___y_549_ = v_a_537_;
v___y_550_ = v_a_538_;
v___y_551_ = v_a_539_;
v___y_552_ = v_a_540_;
goto v___jp_542_;
}
case 7:
{
lean_object* v_binderType_570_; lean_object* v_body_571_; 
v_binderType_570_ = lean_ctor_get(v_e_532_, 1);
v_body_571_ = lean_ctor_get(v_e_532_, 2);
lean_inc_ref(v_body_571_);
lean_inc_ref(v_binderType_570_);
v_t_543_ = v_binderType_570_;
v_b_544_ = v_body_571_;
v___y_545_ = v_a_533_;
v___y_546_ = v_a_534_;
v___y_547_ = v_a_535_;
v___y_548_ = v_a_536_;
v___y_549_ = v_a_537_;
v___y_550_ = v_a_538_;
v___y_551_ = v_a_539_;
v___y_552_ = v_a_540_;
goto v___jp_542_;
}
case 10:
{
lean_object* v_expr_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_expr_572_ = lean_ctor_get(v_e_532_, 1);
lean_inc_ref(v_expr_572_);
v___x_573_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___boxed), 10, 1);
lean_closure_set(v___x_573_, 0, v_expr_572_);
v___x_574_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(v_e_532_, v___x_573_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
return v___x_574_;
}
case 11:
{
lean_object* v_struct_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_struct_575_ = lean_ctor_get(v_e_532_, 2);
lean_inc_ref(v_struct_575_);
v___x_576_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___boxed), 10, 1);
lean_closure_set(v___x_576_, 0, v_struct_575_);
v___x_577_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(v_e_532_, v___x_576_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
return v___x_577_;
}
default: 
{
uint8_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec_ref(v_e_532_);
v___x_578_ = 0;
v___x_579_ = lean_box(v___x_578_);
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
return v___x_580_;
}
}
v___jp_542_:
{
lean_object* v___f_553_; lean_object* v___x_554_; 
v___f_553_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__0___boxed), 11, 2);
lean_closure_set(v___f_553_, 0, v_t_543_);
lean_closure_set(v___f_553_, 1, v_b_544_);
v___x_554_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(v_e_532_, v___f_553_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
return v___x_554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__0(lean_object* v_t_581_, lean_object* v_b_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_t_581_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; uint8_t v___x_594_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
v___x_594_ = lean_unbox(v_a_593_);
lean_dec(v_a_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; 
lean_dec_ref_known(v___x_592_, 1);
v___x_595_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_b_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
return v___x_595_;
}
else
{
lean_dec_ref(v_b_582_);
return v___x_592_;
}
}
else
{
lean_dec_ref(v_b_582_);
return v___x_592_;
}
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___closed__0(void){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1(lean_object* v_msg_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___x_605_; lean_object* v___x_11440__overap_606_; lean_object* v___x_607_; 
v___x_605_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___closed__0);
v___x_11440__overap_606_ = lean_panic_fn_borrowed(v___x_605_, v_msg_597_);
lean_inc(v___y_603_);
lean_inc_ref(v___y_602_);
lean_inc(v___y_601_);
lean_inc_ref(v___y_600_);
lean_inc(v___y_599_);
lean_inc_ref(v___y_598_);
v___x_607_ = lean_apply_7(v___x_11440__overap_606_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, lean_box(0));
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___boxed(lean_object* v_msg_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1(v_msg_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1(lean_object* v_f_617_, lean_object* v_a_618_, lean_object* v___y_619_, uint8_t v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v___y_624_; lean_object* v___y_625_; 
if (v___y_620_ == 0)
{
v___y_624_ = v___y_619_;
v___y_625_ = v___y_622_;
goto v___jp_623_;
}
else
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_617_, v___y_620_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_649_; 
v_a_648_ = lean_ctor_get(v___x_647_, 1);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_647_, 2);
v___x_649_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_618_, v___y_620_, v___y_621_, v_a_648_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; 
v_a_650_ = lean_ctor_get(v___x_649_, 1);
lean_inc(v_a_650_);
lean_dec_ref_known(v___x_649_, 2);
v___y_624_ = v___y_619_;
v___y_625_ = v_a_650_;
goto v___jp_623_;
}
else
{
lean_object* v_a_651_; lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec_ref(v___y_619_);
lean_dec_ref(v_a_618_);
lean_dec_ref(v_f_617_);
v_a_651_ = lean_ctor_get(v___x_649_, 0);
v_a_652_ = lean_ctor_get(v___x_649_, 1);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_649_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_inc(v_a_651_);
lean_dec(v___x_649_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_651_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec_ref(v___y_619_);
lean_dec_ref(v_a_618_);
lean_dec_ref(v_f_617_);
v_a_660_ = lean_ctor_get(v___x_647_, 0);
v_a_661_ = lean_ctor_get(v___x_647_, 1);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_647_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_inc(v_a_660_);
lean_dec(v___x_647_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_660_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
v___jp_623_:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = l_Lean_Expr_app___override(v_f_617_, v_a_618_);
v___x_627_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_626_, v___y_625_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_637_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
v_a_629_ = lean_ctor_get(v___x_627_, 1);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_637_ == 0)
{
v___x_631_ = v___x_627_;
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_inc(v_a_628_);
lean_dec(v___x_627_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v_a_628_);
lean_ctor_set(v___x_633_, 1, v___y_624_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_633_);
v___x_635_ = v___x_631_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_a_629_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
else
{
lean_object* v_a_638_; lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec_ref(v___y_624_);
v_a_638_ = lean_ctor_get(v___x_627_, 0);
v_a_639_ = lean_ctor_get(v___x_627_, 1);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_627_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_inc(v_a_638_);
lean_dec(v___x_627_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_638_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1___boxed(lean_object* v_f_669_, lean_object* v_a_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
uint8_t v___y_34381__boxed_675_; lean_object* v_res_676_; 
v___y_34381__boxed_675_ = lean_unbox(v___y_672_);
v_res_676_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1(v_f_669_, v_a_670_, v___y_671_, v___y_34381__boxed_675_, v___y_673_, v___y_674_);
lean_dec_ref(v___y_673_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(lean_object* v_a_677_, lean_object* v_x_678_){
_start:
{
if (lean_obj_tag(v_x_678_) == 0)
{
lean_object* v___x_679_; 
v___x_679_ = lean_box(0);
return v___x_679_;
}
else
{
lean_object* v_key_680_; lean_object* v_value_681_; lean_object* v_tail_682_; uint8_t v___y_684_; lean_object* v_fst_687_; lean_object* v_snd_688_; lean_object* v_fst_689_; lean_object* v_snd_690_; size_t v___x_691_; size_t v___x_692_; uint8_t v___x_693_; 
v_key_680_ = lean_ctor_get(v_x_678_, 0);
v_value_681_ = lean_ctor_get(v_x_678_, 1);
v_tail_682_ = lean_ctor_get(v_x_678_, 2);
v_fst_687_ = lean_ctor_get(v_key_680_, 0);
v_snd_688_ = lean_ctor_get(v_key_680_, 1);
v_fst_689_ = lean_ctor_get(v_a_677_, 0);
v_snd_690_ = lean_ctor_get(v_a_677_, 1);
v___x_691_ = lean_ptr_addr(v_fst_687_);
v___x_692_ = lean_ptr_addr(v_fst_689_);
v___x_693_ = lean_usize_dec_eq(v___x_691_, v___x_692_);
if (v___x_693_ == 0)
{
v___y_684_ = v___x_693_;
goto v___jp_683_;
}
else
{
uint8_t v___x_694_; 
v___x_694_ = lean_nat_dec_eq(v_snd_688_, v_snd_690_);
v___y_684_ = v___x_694_;
goto v___jp_683_;
}
v___jp_683_:
{
if (v___y_684_ == 0)
{
v_x_678_ = v_tail_682_;
goto _start;
}
else
{
lean_object* v___x_686_; 
lean_inc(v_value_681_);
v___x_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_686_, 0, v_value_681_);
return v___x_686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_a_695_, lean_object* v_x_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_695_, v_x_696_);
lean_dec(v_x_696_);
lean_dec_ref(v_a_695_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___redArg(lean_object* v_m_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_buckets_700_; lean_object* v_fst_701_; lean_object* v_snd_702_; lean_object* v___x_703_; size_t v___x_704_; size_t v___x_705_; size_t v___x_706_; uint64_t v___x_707_; uint64_t v___x_708_; uint64_t v___x_709_; uint64_t v___x_710_; uint64_t v___x_711_; uint64_t v_fold_712_; uint64_t v___x_713_; uint64_t v___x_714_; uint64_t v___x_715_; size_t v___x_716_; size_t v___x_717_; size_t v___x_718_; size_t v___x_719_; size_t v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_buckets_700_ = lean_ctor_get(v_m_698_, 1);
v_fst_701_ = lean_ctor_get(v_a_699_, 0);
v_snd_702_ = lean_ctor_get(v_a_699_, 1);
v___x_703_ = lean_array_get_size(v_buckets_700_);
v___x_704_ = lean_ptr_addr(v_fst_701_);
v___x_705_ = ((size_t)3ULL);
v___x_706_ = lean_usize_shift_right(v___x_704_, v___x_705_);
v___x_707_ = lean_usize_to_uint64(v___x_706_);
v___x_708_ = lean_uint64_of_nat(v_snd_702_);
v___x_709_ = lean_uint64_mix_hash(v___x_707_, v___x_708_);
v___x_710_ = 32ULL;
v___x_711_ = lean_uint64_shift_right(v___x_709_, v___x_710_);
v_fold_712_ = lean_uint64_xor(v___x_709_, v___x_711_);
v___x_713_ = 16ULL;
v___x_714_ = lean_uint64_shift_right(v_fold_712_, v___x_713_);
v___x_715_ = lean_uint64_xor(v_fold_712_, v___x_714_);
v___x_716_ = lean_uint64_to_usize(v___x_715_);
v___x_717_ = lean_usize_of_nat(v___x_703_);
v___x_718_ = ((size_t)1ULL);
v___x_719_ = lean_usize_sub(v___x_717_, v___x_718_);
v___x_720_ = lean_usize_land(v___x_716_, v___x_719_);
v___x_721_ = lean_array_uget_borrowed(v_buckets_700_, v___x_720_);
v___x_722_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_699_, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_723_, lean_object* v_a_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___redArg(v_m_723_, v_a_724_);
lean_dec_ref(v_a_724_);
lean_dec_ref(v_m_723_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7(lean_object* v_msg_733_, lean_object* v___y_734_, uint8_t v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v___f_738_; lean_object* v___f_739_; lean_object* v___f_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___f_752_; lean_object* v___f_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_33971__overap_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___f_738_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__0));
v___f_739_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__1));
v___f_740_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__2));
v___x_741_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__3));
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v___f_738_);
v___x_743_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__4));
v___x_744_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__5));
v___x_745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_745_, 0, v___x_742_);
lean_ctor_set(v___x_745_, 1, v___x_743_);
lean_ctor_set(v___x_745_, 2, v___f_739_);
lean_ctor_set(v___x_745_, 3, v___f_740_);
lean_ctor_set(v___x_745_, 4, v___x_744_);
v___x_746_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__6));
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = l_ReaderT_instMonad___redArg(v___x_747_);
v___x_749_ = l_ReaderT_instMonad___redArg(v___x_748_);
lean_inc_ref_n(v___x_749_, 6);
v___f_750_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_750_, 0, v___x_749_);
v___f_751_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_751_, 0, v___x_749_);
v___f_752_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_752_, 0, v___x_749_);
v___f_753_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_753_, 0, v___x_749_);
v___x_754_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_754_, 0, lean_box(0));
lean_closure_set(v___x_754_, 1, lean_box(0));
lean_closure_set(v___x_754_, 2, v___x_749_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v___f_750_);
v___x_756_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_756_, 0, lean_box(0));
lean_closure_set(v___x_756_, 1, lean_box(0));
lean_closure_set(v___x_756_, 2, v___x_749_);
v___x_757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_757_, 0, v___x_755_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
lean_ctor_set(v___x_757_, 2, v___f_751_);
lean_ctor_set(v___x_757_, 3, v___f_752_);
lean_ctor_set(v___x_757_, 4, v___f_753_);
v___x_758_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_758_, 0, lean_box(0));
lean_closure_set(v___x_758_, 1, lean_box(0));
lean_closure_set(v___x_758_, 2, v___x_749_);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_757_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = l_Lean_instInhabitedExpr;
v___x_761_ = l_instInhabitedOfMonad___redArg(v___x_759_, v___x_760_);
v___x_33971__overap_762_ = lean_panic_fn_borrowed(v___x_761_, v_msg_733_);
lean_dec(v___x_761_);
v___x_763_ = lean_box(v___y_735_);
lean_inc_ref(v___y_736_);
v___x_764_ = lean_apply_4(v___x_33971__overap_762_, v___y_734_, v___x_763_, v___y_736_, v___y_737_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___boxed(lean_object* v_msg_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
uint8_t v___y_34580__boxed_770_; lean_object* v_res_771_; 
v___y_34580__boxed_770_ = lean_unbox(v___y_767_);
v_res_771_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7(v_msg_765_, v___y_766_, v___y_34580__boxed_770_, v___y_768_, v___y_769_);
lean_dec_ref(v___y_768_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__6(lean_object* v_structName_772_, lean_object* v_idx_773_, lean_object* v_struct_774_, lean_object* v___y_775_, uint8_t v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___y_780_; lean_object* v___y_781_; 
if (v___y_776_ == 0)
{
v___y_780_ = v___y_775_;
v___y_781_ = v___y_778_;
goto v___jp_779_;
}
else
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_774_, v___y_776_, v___y_777_, v___y_778_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; 
v_a_804_ = lean_ctor_get(v___x_803_, 1);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 2);
v___y_780_ = v___y_775_;
v___y_781_ = v_a_804_;
goto v___jp_779_;
}
else
{
lean_object* v_a_805_; lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec_ref(v___y_775_);
lean_dec_ref(v_struct_774_);
lean_dec(v_idx_773_);
lean_dec(v_structName_772_);
v_a_805_ = lean_ctor_get(v___x_803_, 0);
v_a_806_ = lean_ctor_get(v___x_803_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_803_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_inc(v_a_805_);
lean_dec(v___x_803_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_805_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
v___jp_779_:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = l_Lean_Expr_proj___override(v_structName_772_, v_idx_773_, v_struct_774_);
v___x_783_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_782_, v___y_781_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_793_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
v_a_785_ = lean_ctor_get(v___x_783_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_793_ == 0)
{
v___x_787_ = v___x_783_;
v_isShared_788_ = v_isSharedCheck_793_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_inc(v_a_784_);
lean_dec(v___x_783_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_793_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v_a_784_);
lean_ctor_set(v___x_789_, 1, v___y_780_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_789_);
v___x_791_ = v___x_787_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_a_785_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
else
{
lean_object* v_a_794_; lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref(v___y_780_);
v_a_794_ = lean_ctor_get(v___x_783_, 0);
v_a_795_ = lean_ctor_get(v___x_783_, 1);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_783_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_inc(v_a_794_);
lean_dec(v___x_783_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_794_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__6___boxed(lean_object* v_structName_814_, lean_object* v_idx_815_, lean_object* v_struct_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
uint8_t v___y_34651__boxed_821_; lean_object* v_res_822_; 
v___y_34651__boxed_821_ = lean_unbox(v___y_818_);
v_res_822_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__6(v_structName_814_, v_idx_815_, v_struct_816_, v___y_817_, v___y_34651__boxed_821_, v___y_819_, v___y_820_);
lean_dec_ref(v___y_819_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4(lean_object* v_x_823_, lean_object* v_t_824_, lean_object* v_v_825_, lean_object* v_b_826_, uint8_t v_nondep_827_, lean_object* v___y_828_, uint8_t v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___y_833_; lean_object* v___y_834_; 
if (v___y_829_ == 0)
{
v___y_833_ = v___y_828_;
v___y_834_ = v___y_831_;
goto v___jp_832_;
}
else
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_824_, v___y_829_, v___y_830_, v___y_831_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_858_; 
v_a_857_ = lean_ctor_get(v___x_856_, 1);
lean_inc(v_a_857_);
lean_dec_ref_known(v___x_856_, 2);
v___x_858_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_825_, v___y_829_, v___y_830_, v_a_857_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; 
v_a_859_ = lean_ctor_get(v___x_858_, 1);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_858_, 2);
v___x_860_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_826_, v___y_829_, v___y_830_, v_a_859_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; 
v_a_861_ = lean_ctor_get(v___x_860_, 1);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 2);
v___y_833_ = v___y_828_;
v___y_834_ = v_a_861_;
goto v___jp_832_;
}
else
{
lean_object* v_a_862_; lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_dec_ref(v___y_828_);
lean_dec_ref(v_b_826_);
lean_dec_ref(v_v_825_);
lean_dec_ref(v_t_824_);
lean_dec(v_x_823_);
v_a_862_ = lean_ctor_get(v___x_860_, 0);
v_a_863_ = lean_ctor_get(v___x_860_, 1);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_860_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_inc(v_a_862_);
lean_dec(v___x_860_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_862_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
else
{
lean_object* v_a_871_; lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec_ref(v___y_828_);
lean_dec_ref(v_b_826_);
lean_dec_ref(v_v_825_);
lean_dec_ref(v_t_824_);
lean_dec(v_x_823_);
v_a_871_ = lean_ctor_get(v___x_858_, 0);
v_a_872_ = lean_ctor_get(v___x_858_, 1);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_858_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_inc(v_a_871_);
lean_dec(v___x_858_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_871_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_object* v_a_880_; lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec_ref(v___y_828_);
lean_dec_ref(v_b_826_);
lean_dec_ref(v_v_825_);
lean_dec_ref(v_t_824_);
lean_dec(v_x_823_);
v_a_880_ = lean_ctor_get(v___x_856_, 0);
v_a_881_ = lean_ctor_get(v___x_856_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_856_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_inc(v_a_880_);
lean_dec(v___x_856_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_880_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
v___jp_832_:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = l_Lean_Expr_letE___override(v_x_823_, v_t_824_, v_v_825_, v_b_826_, v_nondep_827_);
v___x_836_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_835_, v___y_834_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_846_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
v_a_838_ = lean_ctor_get(v___x_836_, 1);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_846_ == 0)
{
v___x_840_ = v___x_836_;
v_isShared_841_ = v_isSharedCheck_846_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_inc(v_a_837_);
lean_dec(v___x_836_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_846_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_842_, 0, v_a_837_);
lean_ctor_set(v___x_842_, 1, v___y_833_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_842_);
v___x_844_ = v___x_840_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_a_838_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
else
{
lean_object* v_a_847_; lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec_ref(v___y_833_);
v_a_847_ = lean_ctor_get(v___x_836_, 0);
v_a_848_ = lean_ctor_get(v___x_836_, 1);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_836_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_inc(v_a_847_);
lean_dec(v___x_836_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_847_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4___boxed(lean_object* v_x_889_, lean_object* v_t_890_, lean_object* v_v_891_, lean_object* v_b_892_, lean_object* v_nondep_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
uint8_t v_nondep_boxed_898_; uint8_t v___y_34734__boxed_899_; lean_object* v_res_900_; 
v_nondep_boxed_898_ = lean_unbox(v_nondep_893_);
v___y_34734__boxed_899_ = lean_unbox(v___y_895_);
v_res_900_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4(v_x_889_, v_t_890_, v_v_891_, v_b_892_, v_nondep_boxed_898_, v___y_894_, v___y_34734__boxed_899_, v___y_896_, v___y_897_);
lean_dec_ref(v___y_896_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2(lean_object* v_x_901_, uint8_t v_bi_902_, lean_object* v_t_903_, lean_object* v_b_904_, lean_object* v___y_905_, uint8_t v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v___y_910_; lean_object* v___y_911_; 
if (v___y_906_ == 0)
{
v___y_910_ = v___y_905_;
v___y_911_ = v___y_908_;
goto v___jp_909_;
}
else
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_903_, v___y_906_, v___y_907_, v___y_908_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_935_; 
v_a_934_ = lean_ctor_get(v___x_933_, 1);
lean_inc(v_a_934_);
lean_dec_ref_known(v___x_933_, 2);
v___x_935_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_904_, v___y_906_, v___y_907_, v_a_934_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; 
v_a_936_ = lean_ctor_get(v___x_935_, 1);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_935_, 2);
v___y_910_ = v___y_905_;
v___y_911_ = v_a_936_;
goto v___jp_909_;
}
else
{
lean_object* v_a_937_; lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec_ref(v___y_905_);
lean_dec_ref(v_b_904_);
lean_dec_ref(v_t_903_);
lean_dec(v_x_901_);
v_a_937_ = lean_ctor_get(v___x_935_, 0);
v_a_938_ = lean_ctor_get(v___x_935_, 1);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_935_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_inc(v_a_937_);
lean_dec(v___x_935_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_937_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
else
{
lean_object* v_a_946_; lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_dec_ref(v___y_905_);
lean_dec_ref(v_b_904_);
lean_dec_ref(v_t_903_);
lean_dec(v_x_901_);
v_a_946_ = lean_ctor_get(v___x_933_, 0);
v_a_947_ = lean_ctor_get(v___x_933_, 1);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_933_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_inc(v_a_946_);
lean_dec(v___x_933_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_946_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
v___jp_909_:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = l_Lean_Expr_lam___override(v_x_901_, v_t_903_, v_b_904_, v_bi_902_);
v___x_913_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_912_, v___y_911_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_923_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_a_915_ = lean_ctor_get(v___x_913_, 1);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_923_ == 0)
{
v___x_917_ = v___x_913_;
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v_a_914_);
lean_ctor_set(v___x_919_, 1, v___y_910_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_919_);
v___x_921_ = v___x_917_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_a_915_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
else
{
lean_object* v_a_924_; lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v___y_910_);
v_a_924_ = lean_ctor_get(v___x_913_, 0);
v_a_925_ = lean_ctor_get(v___x_913_, 1);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_913_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_inc(v_a_924_);
lean_dec(v___x_913_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_924_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_a_925_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2___boxed(lean_object* v_x_955_, lean_object* v_bi_956_, lean_object* v_t_957_, lean_object* v_b_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
uint8_t v_bi_boxed_963_; uint8_t v___y_34863__boxed_964_; lean_object* v_res_965_; 
v_bi_boxed_963_ = lean_unbox(v_bi_956_);
v___y_34863__boxed_964_ = lean_unbox(v___y_960_);
v_res_965_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2(v_x_955_, v_bi_boxed_963_, v_t_957_, v_b_958_, v___y_959_, v___y_34863__boxed_964_, v___y_961_, v___y_962_);
lean_dec_ref(v___y_961_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__5(lean_object* v_d_966_, lean_object* v_e_967_, lean_object* v___y_968_, uint8_t v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___y_973_; lean_object* v___y_974_; 
if (v___y_969_ == 0)
{
v___y_973_ = v___y_968_;
v___y_974_ = v___y_971_;
goto v___jp_972_;
}
else
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_967_, v___y_969_, v___y_970_, v___y_971_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; 
v_a_997_ = lean_ctor_get(v___x_996_, 1);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 2);
v___y_973_ = v___y_968_;
v___y_974_ = v_a_997_;
goto v___jp_972_;
}
else
{
lean_object* v_a_998_; lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec_ref(v___y_968_);
lean_dec_ref(v_e_967_);
lean_dec(v_d_966_);
v_a_998_ = lean_ctor_get(v___x_996_, 0);
v_a_999_ = lean_ctor_get(v___x_996_, 1);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_996_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_inc(v_a_998_);
lean_dec(v___x_996_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_998_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
v___jp_972_:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = l_Lean_Expr_mdata___override(v_d_966_, v_e_967_);
v___x_976_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_975_, v___y_974_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_986_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
v_a_978_ = lean_ctor_get(v___x_976_, 1);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_986_ == 0)
{
v___x_980_ = v___x_976_;
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_inc(v_a_977_);
lean_dec(v___x_976_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_982_, 0, v_a_977_);
lean_ctor_set(v___x_982_, 1, v___y_973_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_982_);
v___x_984_ = v___x_980_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_a_978_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
else
{
lean_object* v_a_987_; lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v___y_973_);
v_a_987_ = lean_ctor_get(v___x_976_, 0);
v_a_988_ = lean_ctor_get(v___x_976_, 1);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_976_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_inc(v_a_987_);
lean_dec(v___x_976_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_987_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__5___boxed(lean_object* v_d_1007_, lean_object* v_e_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
uint8_t v___y_34969__boxed_1013_; lean_object* v_res_1014_; 
v___y_34969__boxed_1013_ = lean_unbox(v___y_1010_);
v_res_1014_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__5(v_d_1007_, v_e_1008_, v___y_1009_, v___y_34969__boxed_1013_, v___y_1011_, v___y_1012_);
lean_dec_ref(v___y_1011_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3(lean_object* v_x_1015_, uint8_t v_bi_1016_, lean_object* v_t_1017_, lean_object* v_b_1018_, lean_object* v___y_1019_, uint8_t v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___y_1024_; lean_object* v___y_1025_; 
if (v___y_1020_ == 0)
{
v___y_1024_ = v___y_1019_;
v___y_1025_ = v___y_1022_;
goto v___jp_1023_;
}
else
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1017_, v___y_1020_, v___y_1021_, v___y_1022_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1049_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 1);
lean_inc(v_a_1048_);
lean_dec_ref_known(v___x_1047_, 2);
v___x_1049_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1018_, v___y_1020_, v___y_1021_, v_a_1048_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 1);
lean_inc(v_a_1050_);
lean_dec_ref_known(v___x_1049_, 2);
v___y_1024_ = v___y_1019_;
v___y_1025_ = v_a_1050_;
goto v___jp_1023_;
}
else
{
lean_object* v_a_1051_; lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec_ref(v___y_1019_);
lean_dec_ref(v_b_1018_);
lean_dec_ref(v_t_1017_);
lean_dec(v_x_1015_);
v_a_1051_ = lean_ctor_get(v___x_1049_, 0);
v_a_1052_ = lean_ctor_get(v___x_1049_, 1);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1049_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_inc(v_a_1051_);
lean_dec(v___x_1049_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1051_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec_ref(v___y_1019_);
lean_dec_ref(v_b_1018_);
lean_dec_ref(v_t_1017_);
lean_dec(v_x_1015_);
v_a_1060_ = lean_ctor_get(v___x_1047_, 0);
v_a_1061_ = lean_ctor_get(v___x_1047_, 1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1047_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_inc(v_a_1060_);
lean_dec(v___x_1047_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1060_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
v___jp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = l_Lean_Expr_forallE___override(v_x_1015_, v_t_1017_, v_b_1018_, v_bi_1016_);
v___x_1027_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1026_, v___y_1025_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1037_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_a_1029_ = lean_ctor_get(v___x_1027_, 1);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1031_ = v___x_1027_;
v_isShared_1032_ = v_isSharedCheck_1037_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1037_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v_a_1028_);
lean_ctor_set(v___x_1033_, 1, v___y_1024_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v___x_1033_);
v___x_1035_ = v___x_1031_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_a_1029_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec_ref(v___y_1024_);
v_a_1038_ = lean_ctor_get(v___x_1027_, 0);
v_a_1039_ = lean_ctor_get(v___x_1027_, 1);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1027_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_inc(v_a_1038_);
lean_dec(v___x_1027_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1038_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3___boxed(lean_object* v_x_1069_, lean_object* v_bi_1070_, lean_object* v_t_1071_, lean_object* v_b_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
uint8_t v_bi_boxed_1077_; uint8_t v___y_35052__boxed_1078_; lean_object* v_res_1079_; 
v_bi_boxed_1077_ = lean_unbox(v_bi_1070_);
v___y_35052__boxed_1078_ = lean_unbox(v___y_1074_);
v_res_1079_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3(v_x_1069_, v_bi_boxed_1077_, v_t_1071_, v_b_1072_, v___y_1073_, v___y_35052__boxed_1078_, v___y_1075_, v___y_1076_);
lean_dec_ref(v___y_1075_);
return v_res_1079_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1083_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_1084_ = lean_unsigned_to_nat(67u);
v___x_1085_ = lean_unsigned_to_nat(35u);
v___x_1086_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__1));
v___x_1087_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__0));
v___x_1088_ = l_mkPanicMessageWithDecl(v___x_1087_, v___x_1086_, v___x_1085_, v___x_1084_, v___x_1083_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0(lean_object* v___x_1089_, lean_object* v___x_1090_, lean_object* v_e_1091_, lean_object* v_offset_1092_, lean_object* v_a_1093_, uint8_t v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
switch(lean_obj_tag(v_e_1091_))
{
case 5:
{
lean_object* v_fn_1097_; lean_object* v_arg_1098_; lean_object* v___x_1099_; 
v_fn_1097_ = lean_ctor_get(v_e_1091_, 0);
v_arg_1098_ = lean_ctor_get(v_e_1091_, 1);
lean_inc(v_offset_1092_);
lean_inc_ref(v_fn_1097_);
v___x_1099_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1089_, v___x_1090_, v_fn_1097_, v_offset_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v_a_1101_; lean_object* v_fst_1102_; lean_object* v_snd_1103_; lean_object* v___x_1104_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
v_a_1101_ = lean_ctor_get(v___x_1099_, 1);
lean_inc(v_a_1101_);
lean_dec_ref_known(v___x_1099_, 2);
v_fst_1102_ = lean_ctor_get(v_a_1100_, 0);
lean_inc(v_fst_1102_);
v_snd_1103_ = lean_ctor_get(v_a_1100_, 1);
lean_inc(v_snd_1103_);
lean_dec(v_a_1100_);
lean_inc_ref(v_arg_1098_);
v___x_1104_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1089_, v___x_1090_, v_arg_1098_, v_offset_1092_, v_snd_1103_, v_a_1094_, v_a_1095_, v_a_1101_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1131_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
v_a_1106_ = lean_ctor_get(v___x_1104_, 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1108_ = v___x_1104_;
v_isShared_1109_ = v_isSharedCheck_1131_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_inc(v_a_1105_);
lean_dec(v___x_1104_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1131_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_fst_1110_; lean_object* v_snd_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1130_; 
v_fst_1110_ = lean_ctor_get(v_a_1105_, 0);
v_snd_1111_ = lean_ctor_get(v_a_1105_, 1);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_a_1105_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1113_ = v_a_1105_;
v_isShared_1114_ = v_isSharedCheck_1130_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_snd_1111_);
lean_inc(v_fst_1110_);
lean_dec(v_a_1105_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1130_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
uint8_t v___y_1116_; size_t v___x_1124_; size_t v___x_1125_; uint8_t v___x_1126_; 
v___x_1124_ = lean_ptr_addr(v_fn_1097_);
v___x_1125_ = lean_ptr_addr(v_fst_1102_);
v___x_1126_ = lean_usize_dec_eq(v___x_1124_, v___x_1125_);
if (v___x_1126_ == 0)
{
v___y_1116_ = v___x_1126_;
goto v___jp_1115_;
}
else
{
size_t v___x_1127_; size_t v___x_1128_; uint8_t v___x_1129_; 
v___x_1127_ = lean_ptr_addr(v_arg_1098_);
v___x_1128_ = lean_ptr_addr(v_fst_1110_);
v___x_1129_ = lean_usize_dec_eq(v___x_1127_, v___x_1128_);
v___y_1116_ = v___x_1129_;
goto v___jp_1115_;
}
v___jp_1115_:
{
if (v___y_1116_ == 0)
{
lean_object* v___x_1117_; 
lean_del_object(v___x_1113_);
lean_del_object(v___x_1108_);
lean_dec_ref_known(v_e_1091_, 2);
v___x_1117_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1(v_fst_1102_, v_fst_1110_, v_snd_1111_, v_a_1094_, v_a_1095_, v_a_1106_);
return v___x_1117_;
}
else
{
lean_object* v___x_1119_; 
lean_dec(v_fst_1110_);
lean_dec(v_fst_1102_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v_e_1091_);
v___x_1119_ = v___x_1113_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_e_1091_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_snd_1111_);
v___x_1119_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1121_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1119_);
v___x_1121_ = v___x_1108_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_a_1106_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1102_);
lean_dec_ref_known(v_e_1091_, 2);
return v___x_1104_;
}
}
else
{
lean_dec_ref_known(v_e_1091_, 2);
lean_dec(v_offset_1092_);
return v___x_1099_;
}
}
case 6:
{
lean_object* v_binderName_1132_; lean_object* v_binderType_1133_; lean_object* v_body_1134_; uint8_t v_binderInfo_1135_; lean_object* v___x_1136_; 
v_binderName_1132_ = lean_ctor_get(v_e_1091_, 0);
v_binderType_1133_ = lean_ctor_get(v_e_1091_, 1);
v_body_1134_ = lean_ctor_get(v_e_1091_, 2);
v_binderInfo_1135_ = lean_ctor_get_uint8(v_e_1091_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1092_);
lean_inc_ref(v_binderType_1133_);
v___x_1136_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1089_, v___x_1090_, v_binderType_1133_, v_offset_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v_a_1138_; lean_object* v_fst_1139_; lean_object* v_snd_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
v_a_1138_ = lean_ctor_get(v___x_1136_, 1);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1136_, 2);
v_fst_1139_ = lean_ctor_get(v_a_1137_, 0);
lean_inc(v_fst_1139_);
v_snd_1140_ = lean_ctor_get(v_a_1137_, 1);
lean_inc(v_snd_1140_);
lean_dec(v_a_1137_);
v___x_1141_ = lean_unsigned_to_nat(1u);
v___x_1142_ = lean_nat_add(v_offset_1092_, v___x_1141_);
lean_dec(v_offset_1092_);
lean_inc_ref(v_body_1134_);
v___x_1143_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1089_, v___x_1090_, v_body_1134_, v___x_1142_, v_snd_1140_, v_a_1094_, v_a_1095_, v_a_1138_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1170_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
v_a_1145_ = lean_ctor_get(v___x_1143_, 1);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1147_ = v___x_1143_;
v_isShared_1148_ = v_isSharedCheck_1170_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_inc(v_a_1144_);
lean_dec(v___x_1143_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1170_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v_fst_1149_; lean_object* v_snd_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1169_; 
v_fst_1149_ = lean_ctor_get(v_a_1144_, 0);
v_snd_1150_ = lean_ctor_get(v_a_1144_, 1);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_a_1144_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1152_ = v_a_1144_;
v_isShared_1153_ = v_isSharedCheck_1169_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_snd_1150_);
lean_inc(v_fst_1149_);
lean_dec(v_a_1144_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1169_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
uint8_t v___y_1155_; size_t v___x_1163_; size_t v___x_1164_; uint8_t v___x_1165_; 
v___x_1163_ = lean_ptr_addr(v_binderType_1133_);
v___x_1164_ = lean_ptr_addr(v_fst_1139_);
v___x_1165_ = lean_usize_dec_eq(v___x_1163_, v___x_1164_);
if (v___x_1165_ == 0)
{
v___y_1155_ = v___x_1165_;
goto v___jp_1154_;
}
else
{
size_t v___x_1166_; size_t v___x_1167_; uint8_t v___x_1168_; 
v___x_1166_ = lean_ptr_addr(v_body_1134_);
v___x_1167_ = lean_ptr_addr(v_fst_1149_);
v___x_1168_ = lean_usize_dec_eq(v___x_1166_, v___x_1167_);
v___y_1155_ = v___x_1168_;
goto v___jp_1154_;
}
v___jp_1154_:
{
if (v___y_1155_ == 0)
{
lean_object* v___x_1156_; 
lean_inc(v_binderName_1132_);
lean_del_object(v___x_1152_);
lean_del_object(v___x_1147_);
lean_dec_ref_known(v_e_1091_, 3);
v___x_1156_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2(v_binderName_1132_, v_binderInfo_1135_, v_fst_1139_, v_fst_1149_, v_snd_1150_, v_a_1094_, v_a_1095_, v_a_1145_);
return v___x_1156_;
}
else
{
lean_object* v___x_1158_; 
lean_dec(v_fst_1149_);
lean_dec(v_fst_1139_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v_e_1091_);
v___x_1158_ = v___x_1152_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_e_1091_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_snd_1150_);
v___x_1158_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1160_; 
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1158_);
v___x_1160_ = v___x_1147_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_a_1145_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1139_);
lean_dec_ref_known(v_e_1091_, 3);
return v___x_1143_;
}
}
else
{
lean_dec_ref_known(v_e_1091_, 3);
lean_dec(v_offset_1092_);
return v___x_1136_;
}
}
case 7:
{
lean_object* v_binderName_1171_; lean_object* v_binderType_1172_; lean_object* v_body_1173_; uint8_t v_binderInfo_1174_; lean_object* v___x_1175_; 
v_binderName_1171_ = lean_ctor_get(v_e_1091_, 0);
v_binderType_1172_ = lean_ctor_get(v_e_1091_, 1);
v_body_1173_ = lean_ctor_get(v_e_1091_, 2);
v_binderInfo_1174_ = lean_ctor_get_uint8(v_e_1091_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1092_);
lean_inc_ref(v_binderType_1172_);
v___x_1175_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1089_, v___x_1090_, v_binderType_1172_, v_offset_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v_a_1177_; lean_object* v_fst_1178_; lean_object* v_snd_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
v_a_1177_ = lean_ctor_get(v___x_1175_, 1);
lean_inc(v_a_1177_);
lean_dec_ref_known(v___x_1175_, 2);
v_fst_1178_ = lean_ctor_get(v_a_1176_, 0);
lean_inc(v_fst_1178_);
v_snd_1179_ = lean_ctor_get(v_a_1176_, 1);
lean_inc(v_snd_1179_);
lean_dec(v_a_1176_);
v___x_1180_ = lean_unsigned_to_nat(1u);
v___x_1181_ = lean_nat_add(v_offset_1092_, v___x_1180_);
lean_dec(v_offset_1092_);
lean_inc_ref(v_body_1173_);
v___x_1182_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1089_, v___x_1090_, v_body_1173_, v___x_1181_, v_snd_1179_, v_a_1094_, v_a_1095_, v_a_1177_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1209_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_a_1184_ = lean_ctor_get(v___x_1182_, 1);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1186_ = v___x_1182_;
v_isShared_1187_ = v_isSharedCheck_1209_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1209_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_fst_1188_; lean_object* v_snd_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1208_; 
v_fst_1188_ = lean_ctor_get(v_a_1183_, 0);
v_snd_1189_ = lean_ctor_get(v_a_1183_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_a_1183_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1191_ = v_a_1183_;
v_isShared_1192_ = v_isSharedCheck_1208_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_snd_1189_);
lean_inc(v_fst_1188_);
lean_dec(v_a_1183_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1208_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
uint8_t v___y_1194_; size_t v___x_1202_; size_t v___x_1203_; uint8_t v___x_1204_; 
v___x_1202_ = lean_ptr_addr(v_binderType_1172_);
v___x_1203_ = lean_ptr_addr(v_fst_1178_);
v___x_1204_ = lean_usize_dec_eq(v___x_1202_, v___x_1203_);
if (v___x_1204_ == 0)
{
v___y_1194_ = v___x_1204_;
goto v___jp_1193_;
}
else
{
size_t v___x_1205_; size_t v___x_1206_; uint8_t v___x_1207_; 
v___x_1205_ = lean_ptr_addr(v_body_1173_);
v___x_1206_ = lean_ptr_addr(v_fst_1188_);
v___x_1207_ = lean_usize_dec_eq(v___x_1205_, v___x_1206_);
v___y_1194_ = v___x_1207_;
goto v___jp_1193_;
}
v___jp_1193_:
{
if (v___y_1194_ == 0)
{
lean_object* v___x_1195_; 
lean_inc(v_binderName_1171_);
lean_del_object(v___x_1191_);
lean_del_object(v___x_1186_);
lean_dec_ref_known(v_e_1091_, 3);
v___x_1195_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3(v_binderName_1171_, v_binderInfo_1174_, v_fst_1178_, v_fst_1188_, v_snd_1189_, v_a_1094_, v_a_1095_, v_a_1184_);
return v___x_1195_;
}
else
{
lean_object* v___x_1197_; 
lean_dec(v_fst_1188_);
lean_dec(v_fst_1178_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v_e_1091_);
v___x_1197_ = v___x_1191_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_e_1091_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_snd_1189_);
v___x_1197_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1199_; 
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1197_);
v___x_1199_ = v___x_1186_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_a_1184_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1178_);
lean_dec_ref_known(v_e_1091_, 3);
return v___x_1182_;
}
}
else
{
lean_dec_ref_known(v_e_1091_, 3);
lean_dec(v_offset_1092_);
return v___x_1175_;
}
}
case 8:
{
lean_object* v_declName_1210_; lean_object* v_type_1211_; lean_object* v_value_1212_; lean_object* v_body_1213_; uint8_t v_nondep_1214_; lean_object* v___x_1215_; 
v_declName_1210_ = lean_ctor_get(v_e_1091_, 0);
v_type_1211_ = lean_ctor_get(v_e_1091_, 1);
v_value_1212_ = lean_ctor_get(v_e_1091_, 2);
v_body_1213_ = lean_ctor_get(v_e_1091_, 3);
v_nondep_1214_ = lean_ctor_get_uint8(v_e_1091_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1092_);
lean_inc_ref(v_type_1211_);
v___x_1215_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1089_, v___x_1090_, v_type_1211_, v_offset_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v_a_1217_; lean_object* v_fst_1218_; lean_object* v_snd_1219_; lean_object* v___x_1220_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
v_a_1217_ = lean_ctor_get(v___x_1215_, 1);
lean_inc(v_a_1217_);
lean_dec_ref_known(v___x_1215_, 2);
v_fst_1218_ = lean_ctor_get(v_a_1216_, 0);
lean_inc(v_fst_1218_);
v_snd_1219_ = lean_ctor_get(v_a_1216_, 1);
lean_inc(v_snd_1219_);
lean_dec(v_a_1216_);
lean_inc(v_offset_1092_);
lean_inc_ref(v_value_1212_);
v___x_1220_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1089_, v___x_1090_, v_value_1212_, v_offset_1092_, v_snd_1219_, v_a_1094_, v_a_1095_, v_a_1217_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v_a_1222_; lean_object* v_fst_1223_; lean_object* v_snd_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
v_a_1222_ = lean_ctor_get(v___x_1220_, 1);
lean_inc(v_a_1222_);
lean_dec_ref_known(v___x_1220_, 2);
v_fst_1223_ = lean_ctor_get(v_a_1221_, 0);
lean_inc(v_fst_1223_);
v_snd_1224_ = lean_ctor_get(v_a_1221_, 1);
lean_inc(v_snd_1224_);
lean_dec(v_a_1221_);
v___x_1225_ = lean_unsigned_to_nat(1u);
v___x_1226_ = lean_nat_add(v_offset_1092_, v___x_1225_);
lean_dec(v_offset_1092_);
lean_inc_ref(v_body_1213_);
v___x_1227_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1089_, v___x_1090_, v_body_1213_, v___x_1226_, v_snd_1224_, v_a_1094_, v_a_1095_, v_a_1222_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1258_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
v_a_1229_ = lean_ctor_get(v___x_1227_, 1);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1231_ = v___x_1227_;
v_isShared_1232_ = v_isSharedCheck_1258_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_inc(v_a_1228_);
lean_dec(v___x_1227_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1258_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v_fst_1233_; lean_object* v_snd_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1257_; 
v_fst_1233_ = lean_ctor_get(v_a_1228_, 0);
v_snd_1234_ = lean_ctor_get(v_a_1228_, 1);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_a_1228_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1236_ = v_a_1228_;
v_isShared_1237_ = v_isSharedCheck_1257_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_snd_1234_);
lean_inc(v_fst_1233_);
lean_dec(v_a_1228_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1257_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
uint8_t v___y_1239_; size_t v___x_1251_; size_t v___x_1252_; uint8_t v___x_1253_; 
v___x_1251_ = lean_ptr_addr(v_type_1211_);
v___x_1252_ = lean_ptr_addr(v_fst_1218_);
v___x_1253_ = lean_usize_dec_eq(v___x_1251_, v___x_1252_);
if (v___x_1253_ == 0)
{
v___y_1239_ = v___x_1253_;
goto v___jp_1238_;
}
else
{
size_t v___x_1254_; size_t v___x_1255_; uint8_t v___x_1256_; 
v___x_1254_ = lean_ptr_addr(v_value_1212_);
v___x_1255_ = lean_ptr_addr(v_fst_1223_);
v___x_1256_ = lean_usize_dec_eq(v___x_1254_, v___x_1255_);
v___y_1239_ = v___x_1256_;
goto v___jp_1238_;
}
v___jp_1238_:
{
if (v___y_1239_ == 0)
{
lean_object* v___x_1240_; 
lean_inc(v_declName_1210_);
lean_del_object(v___x_1236_);
lean_del_object(v___x_1231_);
lean_dec_ref_known(v_e_1091_, 4);
v___x_1240_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4(v_declName_1210_, v_fst_1218_, v_fst_1223_, v_fst_1233_, v_nondep_1214_, v_snd_1234_, v_a_1094_, v_a_1095_, v_a_1229_);
return v___x_1240_;
}
else
{
size_t v___x_1241_; size_t v___x_1242_; uint8_t v___x_1243_; 
v___x_1241_ = lean_ptr_addr(v_body_1213_);
v___x_1242_ = lean_ptr_addr(v_fst_1233_);
v___x_1243_ = lean_usize_dec_eq(v___x_1241_, v___x_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; 
lean_inc(v_declName_1210_);
lean_del_object(v___x_1236_);
lean_del_object(v___x_1231_);
lean_dec_ref_known(v_e_1091_, 4);
v___x_1244_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4(v_declName_1210_, v_fst_1218_, v_fst_1223_, v_fst_1233_, v_nondep_1214_, v_snd_1234_, v_a_1094_, v_a_1095_, v_a_1229_);
return v___x_1244_;
}
else
{
lean_object* v___x_1246_; 
lean_dec(v_fst_1233_);
lean_dec(v_fst_1223_);
lean_dec(v_fst_1218_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v_e_1091_);
v___x_1246_ = v___x_1236_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_e_1091_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_snd_1234_);
v___x_1246_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
lean_object* v___x_1248_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1246_);
v___x_1248_ = v___x_1231_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_a_1229_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1223_);
lean_dec(v_fst_1218_);
lean_dec_ref_known(v_e_1091_, 4);
return v___x_1227_;
}
}
else
{
lean_dec(v_fst_1218_);
lean_dec_ref_known(v_e_1091_, 4);
lean_dec(v_offset_1092_);
return v___x_1220_;
}
}
else
{
lean_dec_ref_known(v_e_1091_, 4);
lean_dec(v_offset_1092_);
return v___x_1215_;
}
}
case 10:
{
lean_object* v_data_1259_; lean_object* v_expr_1260_; lean_object* v___x_1261_; 
v_data_1259_ = lean_ctor_get(v_e_1091_, 0);
v_expr_1260_ = lean_ctor_get(v_e_1091_, 1);
lean_inc_ref(v_expr_1260_);
v___x_1261_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1089_, v___x_1090_, v_expr_1260_, v_offset_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1283_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_a_1263_ = lean_ctor_get(v___x_1261_, 1);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1265_ = v___x_1261_;
v_isShared_1266_ = v_isSharedCheck_1283_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1283_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v_fst_1267_; lean_object* v_snd_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1282_; 
v_fst_1267_ = lean_ctor_get(v_a_1262_, 0);
v_snd_1268_ = lean_ctor_get(v_a_1262_, 1);
v_isSharedCheck_1282_ = !lean_is_exclusive(v_a_1262_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1270_ = v_a_1262_;
v_isShared_1271_ = v_isSharedCheck_1282_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_snd_1268_);
lean_inc(v_fst_1267_);
lean_dec(v_a_1262_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1282_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
size_t v___x_1272_; size_t v___x_1273_; uint8_t v___x_1274_; 
v___x_1272_ = lean_ptr_addr(v_expr_1260_);
v___x_1273_ = lean_ptr_addr(v_fst_1267_);
v___x_1274_ = lean_usize_dec_eq(v___x_1272_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; 
lean_inc(v_data_1259_);
lean_del_object(v___x_1270_);
lean_del_object(v___x_1265_);
lean_dec_ref_known(v_e_1091_, 2);
v___x_1275_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__5(v_data_1259_, v_fst_1267_, v_snd_1268_, v_a_1094_, v_a_1095_, v_a_1263_);
return v___x_1275_;
}
else
{
lean_object* v___x_1277_; 
lean_dec(v_fst_1267_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 0, v_e_1091_);
v___x_1277_ = v___x_1270_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_e_1091_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_snd_1268_);
v___x_1277_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1279_; 
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v___x_1277_);
v___x_1279_ = v___x_1265_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1277_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_a_1263_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1091_, 2);
return v___x_1261_;
}
}
case 11:
{
lean_object* v_typeName_1284_; lean_object* v_idx_1285_; lean_object* v_struct_1286_; lean_object* v___x_1287_; 
v_typeName_1284_ = lean_ctor_get(v_e_1091_, 0);
v_idx_1285_ = lean_ctor_get(v_e_1091_, 1);
v_struct_1286_ = lean_ctor_get(v_e_1091_, 2);
lean_inc_ref(v_struct_1286_);
v___x_1287_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1089_, v___x_1090_, v_struct_1286_, v_offset_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1309_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v_a_1289_ = lean_ctor_get(v___x_1287_, 1);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1291_ = v___x_1287_;
v_isShared_1292_ = v_isSharedCheck_1309_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1309_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v_fst_1293_; lean_object* v_snd_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1308_; 
v_fst_1293_ = lean_ctor_get(v_a_1288_, 0);
v_snd_1294_ = lean_ctor_get(v_a_1288_, 1);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_a_1288_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1296_ = v_a_1288_;
v_isShared_1297_ = v_isSharedCheck_1308_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_snd_1294_);
lean_inc(v_fst_1293_);
lean_dec(v_a_1288_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1308_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
size_t v___x_1298_; size_t v___x_1299_; uint8_t v___x_1300_; 
v___x_1298_ = lean_ptr_addr(v_struct_1286_);
v___x_1299_ = lean_ptr_addr(v_fst_1293_);
v___x_1300_ = lean_usize_dec_eq(v___x_1298_, v___x_1299_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; 
lean_inc(v_idx_1285_);
lean_inc(v_typeName_1284_);
lean_del_object(v___x_1296_);
lean_del_object(v___x_1291_);
lean_dec_ref_known(v_e_1091_, 3);
v___x_1301_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__6(v_typeName_1284_, v_idx_1285_, v_fst_1293_, v_snd_1294_, v_a_1094_, v_a_1095_, v_a_1289_);
return v___x_1301_;
}
else
{
lean_object* v___x_1303_; 
lean_dec(v_fst_1293_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v_e_1091_);
v___x_1303_ = v___x_1296_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_e_1091_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_snd_1294_);
v___x_1303_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1305_; 
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v___x_1303_);
v___x_1305_ = v___x_1291_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_a_1289_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1091_, 3);
return v___x_1287_;
}
}
default: 
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
lean_dec(v_offset_1092_);
lean_dec_ref(v_e_1091_);
v___x_1310_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__3);
v___x_1311_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7(v___x_1310_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
return v___x_1311_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(lean_object* v___x_1312_, lean_object* v___x_1313_, lean_object* v_e_1314_, lean_object* v_offset_1315_, lean_object* v_a_1316_, uint8_t v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v_key_1320_; lean_object* v___x_1321_; 
lean_inc(v_offset_1315_);
lean_inc_ref(v_e_1314_);
v_key_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1320_, 0, v_e_1314_);
lean_ctor_set(v_key_1320_, 1, v_offset_1315_);
v___x_1321_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___redArg(v_a_1316_, v_key_1320_);
if (lean_obj_tag(v___x_1321_) == 1)
{
lean_object* v_val_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_dec_ref_known(v_key_1320_, 2);
lean_dec(v_offset_1315_);
lean_dec_ref(v_e_1314_);
v_val_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_val_1322_);
lean_dec_ref_known(v___x_1321_, 1);
v___x_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1323_, 0, v_val_1322_);
lean_ctor_set(v___x_1323_, 1, v_a_1316_);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
lean_ctor_set(v___x_1324_, 1, v_a_1319_);
return v___x_1324_;
}
else
{
lean_dec(v___x_1321_);
switch(lean_obj_tag(v_e_1314_))
{
case 0:
{
lean_object* v_deBruijnIndex_1325_; uint8_t v___x_1326_; 
v_deBruijnIndex_1325_ = lean_ctor_get(v_e_1314_, 0);
v___x_1326_ = lean_nat_dec_le(v_offset_1315_, v_deBruijnIndex_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
lean_dec(v_offset_1315_);
v___x_1327_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1320_, v_e_1314_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
return v___x_1327_;
}
else
{
lean_object* v_size_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
lean_inc(v_deBruijnIndex_1325_);
lean_dec_ref_known(v_e_1314_, 1);
v_size_1328_ = lean_ctor_get(v___x_1313_, 2);
v___x_1329_ = l_Lean_instInhabitedExpr;
v___x_1330_ = lean_nat_sub(v_deBruijnIndex_1325_, v_offset_1315_);
lean_dec(v_offset_1315_);
lean_dec(v_deBruijnIndex_1325_);
v___x_1331_ = lean_nat_sub(v___x_1312_, v___x_1330_);
lean_dec(v___x_1330_);
v___x_1332_ = lean_unsigned_to_nat(1u);
v___x_1333_ = lean_nat_sub(v___x_1331_, v___x_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_nat_dec_lt(v___x_1333_, v_size_1328_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec(v___x_1333_);
v___x_1335_ = l_outOfBounds___redArg(v___x_1329_);
v___x_1336_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1320_, v___x_1335_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
return v___x_1336_;
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1329_, v___x_1313_, v___x_1333_);
lean_dec(v___x_1333_);
v___x_1338_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1320_, v___x_1337_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
return v___x_1338_;
}
}
}
case 9:
{
lean_object* v___x_1339_; 
lean_dec(v_offset_1315_);
v___x_1339_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1320_, v_e_1314_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
return v___x_1339_;
}
case 2:
{
lean_object* v___x_1340_; 
lean_dec(v_offset_1315_);
v___x_1340_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1320_, v_e_1314_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
return v___x_1340_;
}
case 1:
{
lean_object* v___x_1341_; 
lean_dec(v_offset_1315_);
v___x_1341_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1320_, v_e_1314_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
return v___x_1341_;
}
case 4:
{
lean_object* v___x_1342_; 
lean_dec(v_offset_1315_);
v___x_1342_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1320_, v_e_1314_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
return v___x_1342_;
}
case 3:
{
lean_object* v___x_1343_; 
lean_dec(v_offset_1315_);
v___x_1343_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1320_, v_e_1314_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
return v___x_1343_;
}
default: 
{
lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1344_ = l_Lean_Expr_looseBVarRange(v_e_1314_);
v___x_1345_ = lean_nat_dec_le(v___x_1344_, v_offset_1315_);
lean_dec(v___x_1344_);
if (v___x_1345_ == 0)
{
switch(lean_obj_tag(v_e_1314_))
{
case 9:
{
lean_object* v___x_1346_; 
lean_dec(v_offset_1315_);
v___x_1346_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1320_, v_e_1314_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
return v___x_1346_;
}
case 2:
{
lean_object* v___x_1347_; 
lean_dec(v_offset_1315_);
v___x_1347_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1320_, v_e_1314_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
return v___x_1347_;
}
case 0:
{
lean_object* v___x_1348_; 
lean_dec(v_offset_1315_);
v___x_1348_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1320_, v_e_1314_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
return v___x_1348_;
}
case 1:
{
lean_object* v___x_1349_; 
lean_dec(v_offset_1315_);
v___x_1349_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1320_, v_e_1314_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
return v___x_1349_;
}
case 4:
{
lean_object* v___x_1350_; 
lean_dec(v_offset_1315_);
v___x_1350_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1320_, v_e_1314_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
return v___x_1350_;
}
case 3:
{
lean_object* v___x_1351_; 
lean_dec(v_offset_1315_);
v___x_1351_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1320_, v_e_1314_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
return v___x_1351_;
}
default: 
{
lean_object* v___x_1352_; 
v___x_1352_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0(v___x_1312_, v___x_1313_, v_e_1314_, v_offset_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v_a_1354_; lean_object* v_fst_1355_; lean_object* v_snd_1356_; lean_object* v___x_1357_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1353_);
v_a_1354_ = lean_ctor_get(v___x_1352_, 1);
lean_inc(v_a_1354_);
lean_dec_ref_known(v___x_1352_, 2);
v_fst_1355_ = lean_ctor_get(v_a_1353_, 0);
lean_inc(v_fst_1355_);
v_snd_1356_ = lean_ctor_get(v_a_1353_, 1);
lean_inc(v_snd_1356_);
lean_dec(v_a_1353_);
v___x_1357_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1320_, v_fst_1355_, v_snd_1356_, v_a_1317_, v_a_1318_, v_a_1354_);
return v___x_1357_;
}
else
{
lean_dec_ref_known(v_key_1320_, 2);
return v___x_1352_;
}
}
}
}
else
{
lean_object* v___x_1358_; 
lean_dec(v_offset_1315_);
v___x_1358_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1320_, v_e_1314_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
return v___x_1358_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0___boxed(lean_object* v___x_1359_, lean_object* v___x_1360_, lean_object* v_e_1361_, lean_object* v_offset_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_){
_start:
{
uint8_t v_a_boxed_1367_; lean_object* v_res_1368_; 
v_a_boxed_1367_ = lean_unbox(v_a_1364_);
v_res_1368_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1359_, v___x_1360_, v_e_1361_, v_offset_1362_, v_a_1363_, v_a_boxed_1367_, v_a_1365_, v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec_ref(v___x_1360_);
lean_dec(v___x_1359_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___boxed(lean_object* v___x_1369_, lean_object* v___x_1370_, lean_object* v_e_1371_, lean_object* v_offset_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
uint8_t v_a_boxed_1377_; lean_object* v_res_1378_; 
v_a_boxed_1377_ = lean_unbox(v_a_1374_);
v_res_1378_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0(v___x_1369_, v___x_1370_, v_e_1371_, v_offset_1372_, v_a_1373_, v_a_boxed_1377_, v_a_1375_, v_a_1376_);
lean_dec_ref(v_a_1375_);
lean_dec_ref(v___x_1370_);
lean_dec(v___x_1369_);
return v_res_1378_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1379_ = lean_box(0);
v___x_1380_ = lean_unsigned_to_nat(16u);
v___x_1381_ = lean_mk_array(v___x_1380_, v___x_1379_);
return v___x_1381_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__0, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__0);
v___x_1383_ = lean_unsigned_to_nat(0u);
v___x_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
lean_ctor_set(v___x_1384_, 1, v___x_1382_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0(lean_object* v_e_1385_, lean_object* v_size_1386_, lean_object* v_xs_1387_, uint8_t v_debug_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1385_))
{
case 0:
{
lean_object* v_deBruijnIndex_1392_; uint8_t v___x_1393_; 
v_deBruijnIndex_1392_ = lean_ctor_get(v_e_1385_, 0);
v___x_1393_ = lean_nat_dec_le(v___x_1391_, v_deBruijnIndex_1392_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1394_, 0, v_e_1385_);
lean_ctor_set(v___x_1394_, 1, v___y_1390_);
return v___x_1394_;
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
lean_inc(v_deBruijnIndex_1392_);
lean_dec_ref_known(v_e_1385_, 1);
v___x_1395_ = l_Lean_instInhabitedExpr;
v___x_1396_ = lean_nat_sub(v_size_1386_, v_deBruijnIndex_1392_);
lean_dec(v_deBruijnIndex_1392_);
v___x_1397_ = lean_unsigned_to_nat(1u);
v___x_1398_ = lean_nat_sub(v___x_1396_, v___x_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_nat_dec_lt(v___x_1398_, v_size_1386_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_dec(v___x_1398_);
v___x_1400_ = l_outOfBounds___redArg(v___x_1395_);
v___x_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
lean_ctor_set(v___x_1401_, 1, v___y_1390_);
return v___x_1401_;
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1395_, v_xs_1387_, v___x_1398_);
lean_dec(v___x_1398_);
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
lean_ctor_set(v___x_1403_, 1, v___y_1390_);
return v___x_1403_;
}
}
}
case 9:
{
lean_object* v___x_1404_; 
v___x_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1404_, 0, v_e_1385_);
lean_ctor_set(v___x_1404_, 1, v___y_1390_);
return v___x_1404_;
}
case 2:
{
lean_object* v___x_1405_; 
v___x_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1405_, 0, v_e_1385_);
lean_ctor_set(v___x_1405_, 1, v___y_1390_);
return v___x_1405_;
}
case 1:
{
lean_object* v___x_1406_; 
v___x_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1406_, 0, v_e_1385_);
lean_ctor_set(v___x_1406_, 1, v___y_1390_);
return v___x_1406_;
}
case 4:
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v_e_1385_);
lean_ctor_set(v___x_1407_, 1, v___y_1390_);
return v___x_1407_;
}
case 3:
{
lean_object* v___x_1408_; 
v___x_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1408_, 0, v_e_1385_);
lean_ctor_set(v___x_1408_, 1, v___y_1390_);
return v___x_1408_;
}
default: 
{
lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1409_ = l_Lean_Expr_looseBVarRange(v_e_1385_);
v___x_1410_ = lean_nat_dec_le(v___x_1409_, v___x_1391_);
lean_dec(v___x_1409_);
if (v___x_1410_ == 0)
{
switch(lean_obj_tag(v_e_1385_))
{
case 9:
{
lean_object* v___x_1411_; 
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v_e_1385_);
lean_ctor_set(v___x_1411_, 1, v___y_1390_);
return v___x_1411_;
}
case 2:
{
lean_object* v___x_1412_; 
v___x_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1412_, 0, v_e_1385_);
lean_ctor_set(v___x_1412_, 1, v___y_1390_);
return v___x_1412_;
}
case 0:
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1413_, 0, v_e_1385_);
lean_ctor_set(v___x_1413_, 1, v___y_1390_);
return v___x_1413_;
}
case 1:
{
lean_object* v___x_1414_; 
v___x_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1414_, 0, v_e_1385_);
lean_ctor_set(v___x_1414_, 1, v___y_1390_);
return v___x_1414_;
}
case 4:
{
lean_object* v___x_1415_; 
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v_e_1385_);
lean_ctor_set(v___x_1415_, 1, v___y_1390_);
return v___x_1415_;
}
case 3:
{
lean_object* v___x_1416_; 
v___x_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1416_, 0, v_e_1385_);
lean_ctor_set(v___x_1416_, 1, v___y_1390_);
return v___x_1416_;
}
default: 
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__1);
v___x_1418_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0(v_size_1386_, v_xs_1387_, v_e_1385_, v___x_1391_, v___x_1417_, v_debug_1388_, v___y_1389_, v___y_1390_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1428_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
v_a_1420_ = lean_ctor_get(v___x_1418_, 1);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1422_ = v___x_1418_;
v_isShared_1423_ = v_isSharedCheck_1428_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_inc(v_a_1419_);
lean_dec(v___x_1418_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1428_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v_fst_1424_; lean_object* v___x_1426_; 
v_fst_1424_ = lean_ctor_get(v_a_1419_, 0);
lean_inc(v_fst_1424_);
lean_dec(v_a_1419_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v_fst_1424_);
v___x_1426_ = v___x_1422_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_fst_1424_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_a_1420_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
else
{
lean_object* v_a_1429_; lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
v_a_1429_ = lean_ctor_get(v___x_1418_, 0);
v_a_1430_ = lean_ctor_get(v___x_1418_, 1);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1418_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_inc(v_a_1429_);
lean_dec(v___x_1418_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1429_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
}
else
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1438_, 0, v_e_1385_);
lean_ctor_set(v___x_1438_, 1, v___y_1390_);
return v___x_1438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___boxed(lean_object* v_e_1439_, lean_object* v_size_1440_, lean_object* v_xs_1441_, lean_object* v_debug_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
uint8_t v_debug_boxed_1445_; lean_object* v_res_1446_; 
v_debug_boxed_1445_ = lean_unbox(v_debug_1442_);
v_res_1446_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0(v_e_1439_, v_size_1440_, v_xs_1441_, v_debug_boxed_1445_, v___y_1443_, v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec_ref(v_xs_1441_);
lean_dec(v_size_1440_);
return v_res_1446_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__2(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1449_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_1450_ = lean_unsigned_to_nat(16u);
v___x_1451_ = lean_unsigned_to_nat(62u);
v___x_1452_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__1));
v___x_1453_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__0));
v___x_1454_ = l_mkPanicMessageWithDecl(v___x_1453_, v___x_1452_, v___x_1451_, v___x_1450_, v___x_1449_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(lean_object* v_e_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v_a_1466_; uint8_t v___x_1484_; 
v___x_1484_ = l_Lean_Expr_hasLooseBVars(v_e_1455_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1485_, 0, v_e_1455_);
return v___x_1485_;
}
else
{
lean_object* v___x_1486_; lean_object* v_subst_1487_; lean_object* v___x_1488_; 
v___x_1486_ = lean_st_ref_get(v_a_1457_);
v_subst_1487_ = lean_ctor_get(v___x_1486_, 2);
lean_inc_ref(v_subst_1487_);
lean_dec(v___x_1486_);
v___x_1488_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_subst_1487_, v_e_1455_);
lean_dec_ref(v_subst_1487_);
if (lean_obj_tag(v___x_1488_) == 1)
{
lean_object* v_val_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec_ref(v_e_1455_);
v_val_1489_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1488_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_val_1489_);
lean_dec(v___x_1488_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
lean_ctor_set_tag(v___x_1491_, 0);
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_val_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
else
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v_xs_1499_; lean_object* v_size_1500_; uint8_t v_debug_1501_; lean_object* v_env_1502_; uint8_t v___x_1503_; lean_object* v___x_1504_; lean_object* v___f_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec(v___x_1488_);
v___x_1497_ = lean_st_ref_get(v_a_1459_);
v___x_1498_ = lean_st_ref_get(v_a_1463_);
v_xs_1499_ = lean_ctor_get(v_a_1456_, 0);
v_size_1500_ = lean_ctor_get(v_xs_1499_, 2);
v_debug_1501_ = lean_ctor_get_uint8(v___x_1497_, sizeof(void*)*11);
lean_dec(v___x_1497_);
v_env_1502_ = lean_ctor_get(v___x_1498_, 0);
lean_inc_ref(v_env_1502_);
lean_dec(v___x_1498_);
v___x_1503_ = 0;
v___x_1504_ = lean_box(v_debug_1501_);
lean_inc_ref(v_xs_1499_);
lean_inc(v_size_1500_);
lean_inc_ref(v_e_1455_);
v___f_1505_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1505_, 0, v_e_1455_);
lean_closure_set(v___f_1505_, 1, v_size_1500_);
lean_closure_set(v___f_1505_, 2, v_xs_1499_);
lean_closure_set(v___f_1505_, 3, v___x_1504_);
v___x_1506_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1506_, 0, v_env_1502_);
lean_ctor_set_uint8(v___x_1506_, sizeof(void*)*1, v___x_1503_);
lean_ctor_set_uint8(v___x_1506_, sizeof(void*)*1 + 1, v___x_1503_);
v___x_1507_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1505_, v___x_1506_, v_a_1459_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1508_);
lean_dec_ref_known(v___x_1507_, 1);
if (lean_obj_tag(v_a_1508_) == 0)
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
lean_dec_ref_known(v_a_1508_, 1);
v___x_1509_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__2, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__2_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__2);
v___x_1510_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1(v___x_1509_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref_known(v___x_1510_, 1);
v_a_1466_ = v_a_1511_;
goto v___jp_1465_;
}
else
{
lean_dec_ref(v_e_1455_);
return v___x_1510_;
}
}
else
{
lean_object* v_a_1512_; 
v_a_1512_ = lean_ctor_get(v_a_1508_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v_a_1508_, 1);
v_a_1466_ = v_a_1512_;
goto v___jp_1465_;
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec_ref(v_e_1455_);
v_a_1513_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1507_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1507_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
v___jp_1465_:
{
lean_object* v___x_1467_; lean_object* v_visited_1468_; lean_object* v_types_1469_; lean_object* v_subst_1470_; lean_object* v_visitedClosed_1471_; lean_object* v_hasDepLetCache_1472_; lean_object* v_numConverted_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1483_; 
v___x_1467_ = lean_st_ref_take(v_a_1457_);
v_visited_1468_ = lean_ctor_get(v___x_1467_, 0);
v_types_1469_ = lean_ctor_get(v___x_1467_, 1);
v_subst_1470_ = lean_ctor_get(v___x_1467_, 2);
v_visitedClosed_1471_ = lean_ctor_get(v___x_1467_, 3);
v_hasDepLetCache_1472_ = lean_ctor_get(v___x_1467_, 4);
v_numConverted_1473_ = lean_ctor_get(v___x_1467_, 5);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1475_ = v___x_1467_;
v_isShared_1476_ = v_isSharedCheck_1483_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_numConverted_1473_);
lean_inc(v_hasDepLetCache_1472_);
lean_inc(v_visitedClosed_1471_);
lean_inc(v_subst_1470_);
lean_inc(v_types_1469_);
lean_inc(v_visited_1468_);
lean_dec(v___x_1467_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1483_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; lean_object* v___x_1479_; 
lean_inc_ref(v_a_1466_);
v___x_1477_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_subst_1470_, v_e_1455_, v_a_1466_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 2, v___x_1477_);
v___x_1479_ = v___x_1475_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_visited_1468_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_types_1469_);
lean_ctor_set(v_reuseFailAlloc_1482_, 2, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1482_, 3, v_visitedClosed_1471_);
lean_ctor_set(v_reuseFailAlloc_1482_, 4, v_hasDepLetCache_1472_);
lean_ctor_set(v_reuseFailAlloc_1482_, 5, v_numConverted_1473_);
v___x_1479_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = lean_st_ref_put(v_a_1457_, v___x_1479_);
v___x_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1481_, 0, v_a_1466_);
return v___x_1481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___boxed(lean_object* v_e_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_e_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_);
lean_dec(v_a_1529_);
lean_dec_ref(v_a_1528_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
lean_dec(v_a_1523_);
lean_dec_ref(v_a_1522_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1532_, lean_object* v_m_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___redArg(v_m_1533_, v_a_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1536_, lean_object* v_m_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2(v_00_u03b2_1536_, v_m_1537_, v_a_1538_);
lean_dec_ref(v_a_1538_);
lean_dec_ref(v_m_1537_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_1540_, lean_object* v_a_1541_, lean_object* v_x_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_1541_, v_x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_1544_, lean_object* v_a_1545_, lean_object* v_x_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10(v_00_u03b2_1544_, v_a_1545_, v_x_1546_);
lean_dec(v_x_1546_);
lean_dec_ref(v_a_1545_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(lean_object* v_msgData_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v___x_1554_; lean_object* v_env_1555_; lean_object* v___x_1556_; lean_object* v_mctx_1557_; lean_object* v_lctx_1558_; lean_object* v_options_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1554_ = lean_st_ref_get(v___y_1552_);
v_env_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc_ref(v_env_1555_);
lean_dec(v___x_1554_);
v___x_1556_ = lean_st_ref_get(v___y_1550_);
v_mctx_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc_ref(v_mctx_1557_);
lean_dec(v___x_1556_);
v_lctx_1558_ = lean_ctor_get(v___y_1549_, 2);
v_options_1559_ = lean_ctor_get(v___y_1551_, 2);
lean_inc_ref(v_options_1559_);
lean_inc_ref(v_lctx_1558_);
v___x_1560_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1560_, 0, v_env_1555_);
lean_ctor_set(v___x_1560_, 1, v_mctx_1557_);
lean_ctor_set(v___x_1560_, 2, v_lctx_1558_);
lean_ctor_set(v___x_1560_, 3, v_options_1559_);
v___x_1561_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
lean_ctor_set(v___x_1561_, 1, v_msgData_1548_);
v___x_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0___boxed(lean_object* v_msgData_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(v_msgData_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(lean_object* v_msg_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_ref_1576_; lean_object* v___x_1577_; lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1586_; 
v_ref_1576_ = lean_ctor_get(v___y_1573_, 5);
v___x_1577_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(v_msg_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1580_ = v___x_1577_;
v_isShared_1581_ = v_isSharedCheck_1586_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1577_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1586_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v___x_1584_; 
lean_inc(v_ref_1576_);
v___x_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1582_, 0, v_ref_1576_);
lean_ctor_set(v___x_1582_, 1, v_a_1578_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set_tag(v___x_1580_, 1);
lean_ctor_set(v___x_1580_, 0, v___x_1582_);
v___x_1584_ = v___x_1580_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg___boxed(lean_object* v_msg_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v_msg_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
return v_res_1593_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__0));
v___x_1596_ = l_Lean_stringToMessageData(v___x_1595_);
return v___x_1596_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3(void){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__2));
v___x_1599_ = l_Lean_stringToMessageData(v___x_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(lean_object* v_t_1600_, lean_object* v_s_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
size_t v___x_1611_; size_t v___x_1612_; uint8_t v___x_1613_; 
v___x_1611_ = lean_ptr_addr(v_t_1600_);
v___x_1612_ = lean_ptr_addr(v_s_1601_);
v___x_1613_ = lean_usize_dec_eq(v___x_1611_, v___x_1612_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; 
lean_inc_ref(v_s_1601_);
lean_inc_ref(v_t_1600_);
v___x_1614_ = l_Lean_Meta_isExprDefEq(v_t_1600_, v_s_1601_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1632_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1632_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1632_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
uint8_t v___x_1619_; 
v___x_1619_ = lean_unbox(v_a_1615_);
lean_dec(v_a_1615_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_del_object(v___x_1617_);
v___x_1620_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1);
v___x_1621_ = l_Lean_indentExpr(v_t_1600_);
v___x_1622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1620_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3);
v___x_1624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1622_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = l_Lean_indentExpr(v_s_1601_);
v___x_1626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1624_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v___x_1626_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_);
return v___x_1627_;
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1630_; 
lean_dec_ref(v_s_1601_);
lean_dec_ref(v_t_1600_);
v___x_1628_ = lean_box(0);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v___x_1628_);
v___x_1630_ = v___x_1617_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec_ref(v_s_1601_);
lean_dec_ref(v_t_1600_);
v_a_1633_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1614_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1614_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
lean_dec_ref(v_s_1601_);
lean_dec_ref(v_t_1600_);
v___x_1641_ = lean_box(0);
v___x_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
return v___x_1642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___boxed(lean_object* v_t_1643_, lean_object* v_s_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_t_1643_, v_s_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0(lean_object* v_00_u03b1_1655_, lean_object* v_msg_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v_msg_1656_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___boxed(lean_object* v_00_u03b1_1667_, lean_object* v_msg_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0(v_00_u03b1_1667_, v_msg_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
return v_res_1678_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__0));
v___x_1681_ = l_Lean_stringToMessageData(v___x_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(lean_object* v_type_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
uint8_t v___x_1690_; 
v___x_1690_ = l_Lean_Expr_isForall(v_type_1682_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; 
lean_inc(v_a_1688_);
lean_inc_ref(v_a_1687_);
lean_inc(v_a_1686_);
lean_inc_ref(v_a_1685_);
v___x_1691_ = lean_whnf(v_type_1682_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; uint8_t v___x_1693_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1691_, 1);
v___x_1693_ = l_Lean_Expr_isForall(v_a_1692_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
v___x_1694_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1);
v___x_1695_ = l_Lean_indentExpr(v_a_1692_);
v___x_1696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v___x_1696_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_);
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
else
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_Meta_Sym_shareCommon(v_a_1692_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_);
return v___x_1706_;
}
}
else
{
return v___x_1691_;
}
}
else
{
lean_object* v___x_1707_; 
v___x_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1707_, 0, v_type_1682_);
return v___x_1707_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___boxed(lean_object* v_type_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_type_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall(lean_object* v_type_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_type_1717_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___boxed(lean_object* v_type_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall(v_type_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
lean_dec(v_a_1732_);
lean_dec_ref(v_a_1731_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
return v_res_1738_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_isClean(lean_object* v_e_1739_, lean_object* v_ctx_1740_){
_start:
{
lean_object* v_cleanSuffix_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v_cleanSuffix_1741_ = lean_ctor_get(v_ctx_1740_, 2);
v___x_1742_ = l_Lean_Expr_looseBVarRange(v_e_1739_);
v___x_1743_ = lean_nat_dec_le(v___x_1742_, v_cleanSuffix_1741_);
lean_dec(v___x_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_isClean___boxed(lean_object* v_e_1744_, lean_object* v_ctx_1745_){
_start:
{
uint8_t v_res_1746_; lean_object* v_r_1747_; 
v_res_1746_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_isClean(v_e_1744_, v_ctx_1745_);
lean_dec_ref(v_ctx_1745_);
lean_dec_ref(v_e_1744_);
v_r_1747_ = lean_box(v_res_1746_);
return v_r_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(lean_object* v_e_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_e_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v_keyedConfig_1760_; uint8_t v_trackZetaDelta_1761_; lean_object* v_zetaDeltaSet_1762_; lean_object* v_lctx_1763_; lean_object* v_localInstances_1764_; lean_object* v_defEqCtx_x3f_1765_; lean_object* v_synthPendingDepth_1766_; lean_object* v_customCanUnfoldPredicate_x3f_1767_; uint8_t v_univApprox_1768_; uint8_t v_inTypeClassResolution_1769_; uint8_t v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 1);
v_keyedConfig_1760_ = lean_ctor_get(v_a_1753_, 0);
v_trackZetaDelta_1761_ = lean_ctor_get_uint8(v_a_1753_, sizeof(void*)*7);
v_zetaDeltaSet_1762_ = lean_ctor_get(v_a_1753_, 1);
v_lctx_1763_ = lean_ctor_get(v_a_1753_, 2);
v_localInstances_1764_ = lean_ctor_get(v_a_1753_, 3);
v_defEqCtx_x3f_1765_ = lean_ctor_get(v_a_1753_, 4);
v_synthPendingDepth_1766_ = lean_ctor_get(v_a_1753_, 5);
v_customCanUnfoldPredicate_x3f_1767_ = lean_ctor_get(v_a_1753_, 6);
v_univApprox_1768_ = lean_ctor_get_uint8(v_a_1753_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1769_ = lean_ctor_get_uint8(v_a_1753_, sizeof(void*)*7 + 2);
v___x_1770_ = 0;
lean_inc(v_customCanUnfoldPredicate_x3f_1767_);
lean_inc(v_synthPendingDepth_1766_);
lean_inc(v_defEqCtx_x3f_1765_);
lean_inc_ref(v_localInstances_1764_);
lean_inc_ref(v_lctx_1763_);
lean_inc(v_zetaDeltaSet_1762_);
lean_inc_ref(v_keyedConfig_1760_);
v___x_1771_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1771_, 0, v_keyedConfig_1760_);
lean_ctor_set(v___x_1771_, 1, v_zetaDeltaSet_1762_);
lean_ctor_set(v___x_1771_, 2, v_lctx_1763_);
lean_ctor_set(v___x_1771_, 3, v_localInstances_1764_);
lean_ctor_set(v___x_1771_, 4, v_defEqCtx_x3f_1765_);
lean_ctor_set(v___x_1771_, 5, v_synthPendingDepth_1766_);
lean_ctor_set(v___x_1771_, 6, v_customCanUnfoldPredicate_x3f_1767_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*7, v_trackZetaDelta_1761_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*7 + 1, v_univApprox_1768_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1769_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*7 + 3, v___x_1770_);
lean_inc(v_a_1756_);
lean_inc_ref(v_a_1755_);
lean_inc(v_a_1754_);
v___x_1772_ = lean_infer_type(v_a_1759_, v___x_1771_, v_a_1754_, v_a_1755_, v_a_1756_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1774_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1772_, 1);
v___x_1774_ = l_Lean_Meta_Sym_shareCommon(v_a_1773_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_);
return v___x_1774_;
}
else
{
return v___x_1772_;
}
}
else
{
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback___boxed(lean_object* v_e_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(v_e_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
lean_dec(v_a_1779_);
lean_dec_ref(v_a_1778_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
return v_res_1785_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_instMonadEIO(lean_box(0));
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(lean_object* v_msg_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v_toApplicative_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1868_; 
v___x_1801_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0);
v___x_1802_ = l_StateRefT_x27_instMonad___redArg(v___x_1801_);
v_toApplicative_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1868_ == 0)
{
lean_object* v_unused_1869_; 
v_unused_1869_ = lean_ctor_get(v___x_1802_, 1);
lean_dec(v_unused_1869_);
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1868_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_toApplicative_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1868_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v_toFunctor_1807_; lean_object* v_toSeq_1808_; lean_object* v_toSeqLeft_1809_; lean_object* v_toSeqRight_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1866_; 
v_toFunctor_1807_ = lean_ctor_get(v_toApplicative_1803_, 0);
v_toSeq_1808_ = lean_ctor_get(v_toApplicative_1803_, 2);
v_toSeqLeft_1809_ = lean_ctor_get(v_toApplicative_1803_, 3);
v_toSeqRight_1810_ = lean_ctor_get(v_toApplicative_1803_, 4);
v_isSharedCheck_1866_ = !lean_is_exclusive(v_toApplicative_1803_);
if (v_isSharedCheck_1866_ == 0)
{
lean_object* v_unused_1867_; 
v_unused_1867_ = lean_ctor_get(v_toApplicative_1803_, 1);
lean_dec(v_unused_1867_);
v___x_1812_ = v_toApplicative_1803_;
v_isShared_1813_ = v_isSharedCheck_1866_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_toSeqRight_1810_);
lean_inc(v_toSeqLeft_1809_);
lean_inc(v_toSeq_1808_);
lean_inc(v_toFunctor_1807_);
lean_dec(v_toApplicative_1803_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1866_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___f_1814_; lean_object* v___f_1815_; lean_object* v___f_1816_; lean_object* v___f_1817_; lean_object* v___x_1818_; lean_object* v___f_1819_; lean_object* v___f_1820_; lean_object* v___f_1821_; lean_object* v___x_1823_; 
v___f_1814_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__1));
v___f_1815_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1807_);
v___f_1816_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1816_, 0, v_toFunctor_1807_);
v___f_1817_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1817_, 0, v_toFunctor_1807_);
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___f_1816_);
lean_ctor_set(v___x_1818_, 1, v___f_1817_);
v___f_1819_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1819_, 0, v_toSeqRight_1810_);
v___f_1820_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1820_, 0, v_toSeqLeft_1809_);
v___f_1821_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1821_, 0, v_toSeq_1808_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 4, v___f_1819_);
lean_ctor_set(v___x_1812_, 3, v___f_1820_);
lean_ctor_set(v___x_1812_, 2, v___f_1821_);
lean_ctor_set(v___x_1812_, 1, v___f_1814_);
lean_ctor_set(v___x_1812_, 0, v___x_1818_);
v___x_1823_ = v___x_1812_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1818_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v___f_1814_);
lean_ctor_set(v_reuseFailAlloc_1865_, 2, v___f_1821_);
lean_ctor_set(v_reuseFailAlloc_1865_, 3, v___f_1820_);
lean_ctor_set(v_reuseFailAlloc_1865_, 4, v___f_1819_);
v___x_1823_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1825_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 1, v___f_1815_);
lean_ctor_set(v___x_1805_, 0, v___x_1823_);
v___x_1825_ = v___x_1805_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v___f_1815_);
v___x_1825_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1826_; lean_object* v_toApplicative_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1862_; 
v___x_1826_ = l_StateRefT_x27_instMonad___redArg(v___x_1825_);
v_toApplicative_1827_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; 
v_unused_1863_ = lean_ctor_get(v___x_1826_, 1);
lean_dec(v_unused_1863_);
v___x_1829_ = v___x_1826_;
v_isShared_1830_ = v_isSharedCheck_1862_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_toApplicative_1827_);
lean_dec(v___x_1826_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1862_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v_toFunctor_1831_; lean_object* v_toSeq_1832_; lean_object* v_toSeqLeft_1833_; lean_object* v_toSeqRight_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1860_; 
v_toFunctor_1831_ = lean_ctor_get(v_toApplicative_1827_, 0);
v_toSeq_1832_ = lean_ctor_get(v_toApplicative_1827_, 2);
v_toSeqLeft_1833_ = lean_ctor_get(v_toApplicative_1827_, 3);
v_toSeqRight_1834_ = lean_ctor_get(v_toApplicative_1827_, 4);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_toApplicative_1827_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; 
v_unused_1861_ = lean_ctor_get(v_toApplicative_1827_, 1);
lean_dec(v_unused_1861_);
v___x_1836_ = v_toApplicative_1827_;
v_isShared_1837_ = v_isSharedCheck_1860_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_toSeqRight_1834_);
lean_inc(v_toSeqLeft_1833_);
lean_inc(v_toSeq_1832_);
lean_inc(v_toFunctor_1831_);
lean_dec(v_toApplicative_1827_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1860_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___f_1838_; lean_object* v___f_1839_; lean_object* v___f_1840_; lean_object* v___f_1841_; lean_object* v___x_1842_; lean_object* v___f_1843_; lean_object* v___f_1844_; lean_object* v___f_1845_; lean_object* v___x_1847_; 
v___f_1838_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__3));
v___f_1839_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1831_);
v___f_1840_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1840_, 0, v_toFunctor_1831_);
v___f_1841_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1841_, 0, v_toFunctor_1831_);
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___f_1840_);
lean_ctor_set(v___x_1842_, 1, v___f_1841_);
v___f_1843_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1843_, 0, v_toSeqRight_1834_);
v___f_1844_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1844_, 0, v_toSeqLeft_1833_);
v___f_1845_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1845_, 0, v_toSeq_1832_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 4, v___f_1843_);
lean_ctor_set(v___x_1836_, 3, v___f_1844_);
lean_ctor_set(v___x_1836_, 2, v___f_1845_);
lean_ctor_set(v___x_1836_, 1, v___f_1838_);
lean_ctor_set(v___x_1836_, 0, v___x_1842_);
v___x_1847_ = v___x_1836_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v___f_1838_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v___f_1845_);
lean_ctor_set(v_reuseFailAlloc_1859_, 3, v___f_1844_);
lean_ctor_set(v_reuseFailAlloc_1859_, 4, v___f_1843_);
v___x_1847_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1849_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 1, v___f_1839_);
lean_ctor_set(v___x_1829_, 0, v___x_1847_);
v___x_1849_ = v___x_1829_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1847_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v___f_1839_);
v___x_1849_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___f_1855_; lean_object* v___x_12506__overap_1856_; lean_object* v___x_1857_; 
v___x_1850_ = l_StateRefT_x27_instMonad___redArg(v___x_1849_);
v___x_1851_ = l_ReaderT_instMonad___redArg(v___x_1850_);
v___x_1852_ = l_StateRefT_x27_instMonad___redArg(v___x_1851_);
v___x_1853_ = l_Lean_instInhabitedExpr;
v___x_1854_ = l_instInhabitedOfMonad___redArg(v___x_1852_, v___x_1853_);
v___f_1855_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1855_, 0, v___x_1854_);
v___x_12506__overap_1856_ = lean_panic_fn_borrowed(v___f_1855_, v_msg_1791_);
lean_dec_ref(v___f_1855_);
lean_inc(v___y_1799_);
lean_inc_ref(v___y_1798_);
lean_inc(v___y_1797_);
lean_inc_ref(v___y_1796_);
lean_inc(v___y_1795_);
lean_inc_ref(v___y_1794_);
lean_inc(v___y_1793_);
lean_inc_ref(v___y_1792_);
v___x_1857_ = lean_apply_9(v___x_12506__overap_1856_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, lean_box(0));
return v___x_1857_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___boxed(lean_object* v_msg_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(v_msg_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
return v_res_1880_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2(void){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1883_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_1884_ = lean_unsigned_to_nat(44u);
v___x_1885_ = lean_unsigned_to_nat(367u);
v___x_1886_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__1));
v___x_1887_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0));
v___x_1888_ = l_mkPanicMessageWithDecl(v___x_1887_, v___x_1886_, v___x_1885_, v___x_1884_, v___x_1883_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(lean_object* v_e_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v_type_1900_; lean_object* v___y_1901_; uint8_t v___x_1919_; 
v___x_1919_ = l_Lean_Expr_hasLooseBVars(v_e_1889_);
if (v___x_1919_ == 0)
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_Meta_Sym_inferType(v_e_1889_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
return v___x_1920_;
}
else
{
lean_object* v___x_1921_; lean_object* v___y_1923_; lean_object* v_types_1927_; lean_object* v___x_1928_; 
v___x_1921_ = lean_st_ref_get(v_a_1891_);
v_types_1927_ = lean_ctor_get(v___x_1921_, 1);
lean_inc_ref(v_types_1927_);
lean_dec(v___x_1921_);
v___x_1928_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_types_1927_, v_e_1889_);
lean_dec_ref(v_types_1927_);
if (lean_obj_tag(v___x_1928_) == 1)
{
lean_object* v_val_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec_ref(v_e_1889_);
v_val_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_val_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set_tag(v___x_1931_, 0);
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_val_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
else
{
lean_dec(v___x_1928_);
switch(lean_obj_tag(v_e_1889_))
{
case 0:
{
lean_object* v_xs_1937_; lean_object* v_deBruijnIndex_1938_; lean_object* v_size_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v_xs_1937_ = lean_ctor_get(v_a_1890_, 0);
v_deBruijnIndex_1938_ = lean_ctor_get(v_e_1889_, 0);
v_size_1939_ = lean_ctor_get(v_xs_1937_, 2);
v___x_1940_ = l_Lean_instInhabitedExpr;
v___x_1941_ = lean_nat_sub(v_size_1939_, v_deBruijnIndex_1938_);
v___x_1942_ = lean_unsigned_to_nat(1u);
v___x_1943_ = lean_nat_sub(v___x_1941_, v___x_1942_);
lean_dec(v___x_1941_);
v___x_1944_ = lean_nat_dec_lt(v___x_1943_, v_size_1939_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; 
lean_dec(v___x_1943_);
v___x_1945_ = l_outOfBounds___redArg(v___x_1940_);
v___y_1923_ = v___x_1945_;
goto v___jp_1922_;
}
else
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1940_, v_xs_1937_, v___x_1943_);
lean_dec(v___x_1943_);
v___y_1923_ = v___x_1946_;
goto v___jp_1922_;
}
}
case 10:
{
lean_object* v_expr_1947_; lean_object* v___x_1948_; 
v_expr_1947_ = lean_ctor_get(v_e_1889_, 1);
lean_inc_ref(v_expr_1947_);
v___x_1948_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_expr_1947_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
lean_dec_ref_known(v___x_1948_, 1);
v_type_1900_ = v_a_1949_;
v___y_1901_ = v_a_1891_;
goto v___jp_1899_;
}
else
{
lean_dec_ref_known(v_e_1889_, 2);
return v___x_1948_;
}
}
case 5:
{
lean_object* v_fn_1950_; lean_object* v_arg_1951_; lean_object* v___x_1952_; 
v_fn_1950_ = lean_ctor_get(v_e_1889_, 0);
v_arg_1951_ = lean_ctor_get(v_e_1889_, 1);
lean_inc_ref(v_fn_1950_);
v___x_1952_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_fn_1950_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1954_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref_known(v___x_1952_, 1);
v___x_1954_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_a_1953_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___x_1954_, 1);
if (lean_obj_tag(v_a_1955_) == 7)
{
lean_object* v_body_1956_; uint8_t v___x_1957_; 
v_body_1956_ = lean_ctor_get(v_a_1955_, 2);
lean_inc_ref(v_body_1956_);
lean_dec_ref_known(v_a_1955_, 3);
v___x_1957_ = l_Lean_Expr_hasLooseBVars(v_body_1956_);
if (v___x_1957_ == 0)
{
v_type_1900_ = v_body_1956_;
v___y_1901_ = v_a_1891_;
goto v___jp_1899_;
}
else
{
lean_object* v___x_1958_; 
lean_inc_ref(v_arg_1951_);
v___x_1958_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_arg_1951_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1958_, 1);
v___x_1960_ = lean_expr_instantiate1(v_body_1956_, v_a_1959_);
lean_dec(v_a_1959_);
lean_dec_ref(v_body_1956_);
v___x_1961_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1960_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1962_);
lean_dec_ref_known(v___x_1961_, 1);
v_type_1900_ = v_a_1962_;
v___y_1901_ = v_a_1891_;
goto v___jp_1899_;
}
else
{
lean_dec_ref_known(v_e_1889_, 2);
return v___x_1961_;
}
}
else
{
lean_dec_ref(v_body_1956_);
lean_dec_ref_known(v_e_1889_, 2);
return v___x_1958_;
}
}
}
else
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
lean_dec(v_a_1955_);
v___x_1963_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2);
v___x_1964_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(v___x_1963_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref_known(v___x_1964_, 1);
v_type_1900_ = v_a_1965_;
v___y_1901_ = v_a_1891_;
goto v___jp_1899_;
}
else
{
lean_dec_ref_known(v_e_1889_, 2);
return v___x_1964_;
}
}
}
else
{
lean_dec_ref_known(v_e_1889_, 2);
return v___x_1954_;
}
}
else
{
lean_dec_ref_known(v_e_1889_, 2);
return v___x_1952_;
}
}
default: 
{
lean_object* v___x_1966_; 
lean_inc_ref(v_e_1889_);
v___x_1966_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(v_e_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
v_type_1900_ = v_a_1967_;
v___y_1901_ = v_a_1891_;
goto v___jp_1899_;
}
else
{
lean_dec_ref(v_e_1889_);
return v___x_1966_;
}
}
}
}
v___jp_1922_:
{
lean_object* v_lctx_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_lctx_1924_ = lean_ctor_get(v_a_1894_, 2);
lean_inc_ref(v_lctx_1924_);
v___x_1925_ = l_Lean_LocalContext_getFVar_x21(v_lctx_1924_, v___y_1923_);
lean_dec_ref(v___y_1923_);
v___x_1926_ = l_Lean_LocalDecl_type(v___x_1925_);
lean_dec_ref(v___x_1925_);
v_type_1900_ = v___x_1926_;
v___y_1901_ = v_a_1891_;
goto v___jp_1899_;
}
}
v___jp_1899_:
{
lean_object* v___x_1902_; lean_object* v_visited_1903_; lean_object* v_types_1904_; lean_object* v_subst_1905_; lean_object* v_visitedClosed_1906_; lean_object* v_hasDepLetCache_1907_; lean_object* v_numConverted_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1918_; 
v___x_1902_ = lean_st_ref_take(v___y_1901_);
v_visited_1903_ = lean_ctor_get(v___x_1902_, 0);
v_types_1904_ = lean_ctor_get(v___x_1902_, 1);
v_subst_1905_ = lean_ctor_get(v___x_1902_, 2);
v_visitedClosed_1906_ = lean_ctor_get(v___x_1902_, 3);
v_hasDepLetCache_1907_ = lean_ctor_get(v___x_1902_, 4);
v_numConverted_1908_ = lean_ctor_get(v___x_1902_, 5);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1910_ = v___x_1902_;
v_isShared_1911_ = v_isSharedCheck_1918_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_numConverted_1908_);
lean_inc(v_hasDepLetCache_1907_);
lean_inc(v_visitedClosed_1906_);
lean_inc(v_subst_1905_);
lean_inc(v_types_1904_);
lean_inc(v_visited_1903_);
lean_dec(v___x_1902_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1918_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1912_; lean_object* v___x_1914_; 
lean_inc_ref(v_type_1900_);
v___x_1912_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_types_1904_, v_e_1889_, v_type_1900_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 1, v___x_1912_);
v___x_1914_ = v___x_1910_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_visited_1903_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v___x_1912_);
lean_ctor_set(v_reuseFailAlloc_1917_, 2, v_subst_1905_);
lean_ctor_set(v_reuseFailAlloc_1917_, 3, v_visitedClosed_1906_);
lean_ctor_set(v_reuseFailAlloc_1917_, 4, v_hasDepLetCache_1907_);
lean_ctor_set(v_reuseFailAlloc_1917_, 5, v_numConverted_1908_);
v___x_1914_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = lean_st_ref_put(v___y_1901_, v___x_1914_);
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_type_1900_);
return v___x_1916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___boxed(lean_object* v_e_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_e_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
lean_dec(v_a_1970_);
lean_dec_ref(v_a_1969_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(lean_object* v_fvarId_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = l_Lean_Expr_fvar___override(v_fvarId_1979_);
v___x_1983_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1982_, v___y_1980_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg___boxed(lean_object* v_fvarId_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(v_fvarId_1984_, v___y_1985_);
lean_dec(v___y_1985_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1(lean_object* v_fvarId_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(v_fvarId_1988_, v___y_1992_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___boxed(lean_object* v_fvarId_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1(v_fvarId_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0(lean_object* v_x_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v___x_2020_; 
lean_inc(v___y_2014_);
lean_inc_ref(v___y_2013_);
lean_inc(v___y_2012_);
lean_inc_ref(v___y_2011_);
v___x_2020_ = lean_apply_9(v_x_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, lean_box(0));
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0___boxed(lean_object* v_x_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0(v_x_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(lean_object* v_lctx_2032_, lean_object* v_localInsts_2033_, lean_object* v_x_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v___f_2044_; lean_object* v___x_2045_; 
lean_inc(v___y_2038_);
lean_inc_ref(v___y_2037_);
lean_inc(v___y_2036_);
lean_inc_ref(v___y_2035_);
v___f_2044_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2044_, 0, v_x_2034_);
lean_closure_set(v___f_2044_, 1, v___y_2035_);
lean_closure_set(v___f_2044_, 2, v___y_2036_);
lean_closure_set(v___f_2044_, 3, v___y_2037_);
lean_closure_set(v___f_2044_, 4, v___y_2038_);
v___x_2045_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2032_, v_localInsts_2033_, v___f_2044_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2045_) == 0)
{
return v___x_2045_;
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_2045_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___boxed(lean_object* v_lctx_2054_, lean_object* v_localInsts_2055_, lean_object* v_x_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(v_lctx_2054_, v_localInsts_2055_, v_x_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2(lean_object* v_00_u03b1_2067_, lean_object* v_lctx_2068_, lean_object* v_localInsts_2069_, lean_object* v_x_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(v_lctx_2068_, v_localInsts_2069_, v_x_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___boxed(lean_object* v_00_u03b1_2081_, lean_object* v_lctx_2082_, lean_object* v_localInsts_2083_, lean_object* v_x_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2(v_00_u03b1_2081_, v_lctx_2082_, v_localInsts_2083_, v_x_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(lean_object* v___y_2095_, lean_object* v_visited_2096_, lean_object* v_types_2097_, lean_object* v_subst_2098_, lean_object* v_a_x3f_2099_){
_start:
{
lean_object* v___x_2101_; lean_object* v_visitedClosed_2102_; lean_object* v_hasDepLetCache_2103_; lean_object* v_numConverted_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2114_; 
v___x_2101_ = lean_st_ref_take(v___y_2095_);
v_visitedClosed_2102_ = lean_ctor_get(v___x_2101_, 3);
v_hasDepLetCache_2103_ = lean_ctor_get(v___x_2101_, 4);
v_numConverted_2104_ = lean_ctor_get(v___x_2101_, 5);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2114_ == 0)
{
lean_object* v_unused_2115_; lean_object* v_unused_2116_; lean_object* v_unused_2117_; 
v_unused_2115_ = lean_ctor_get(v___x_2101_, 2);
lean_dec(v_unused_2115_);
v_unused_2116_ = lean_ctor_get(v___x_2101_, 1);
lean_dec(v_unused_2116_);
v_unused_2117_ = lean_ctor_get(v___x_2101_, 0);
lean_dec(v_unused_2117_);
v___x_2106_ = v___x_2101_;
v_isShared_2107_ = v_isSharedCheck_2114_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_numConverted_2104_);
lean_inc(v_hasDepLetCache_2103_);
lean_inc(v_visitedClosed_2102_);
lean_dec(v___x_2101_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2114_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 2, v_subst_2098_);
lean_ctor_set(v___x_2106_, 1, v_types_2097_);
lean_ctor_set(v___x_2106_, 0, v_visited_2096_);
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_visited_2096_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_types_2097_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_subst_2098_);
lean_ctor_set(v_reuseFailAlloc_2113_, 3, v_visitedClosed_2102_);
lean_ctor_set(v_reuseFailAlloc_2113_, 4, v_hasDepLetCache_2103_);
lean_ctor_set(v_reuseFailAlloc_2113_, 5, v_numConverted_2104_);
v___x_2109_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2110_ = lean_st_ref_put(v___y_2095_, v___x_2109_);
v___x_2111_ = lean_box(0);
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
return v___x_2112_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0___boxed(lean_object* v___y_2118_, lean_object* v_visited_2119_, lean_object* v_types_2120_, lean_object* v_subst_2121_, lean_object* v_a_x3f_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(v___y_2118_, v_visited_2119_, v_types_2120_, v_subst_2121_, v_a_x3f_2122_);
lean_dec(v_a_x3f_2122_);
lean_dec(v___y_2118_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1(lean_object* v_k_2125_, lean_object* v_a_2126_, uint8_t v_tainted_2127_, uint8_t v_isCandidate_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___y_2139_; lean_object* v_xs_2185_; lean_object* v_numCandidates_2186_; lean_object* v_cleanSuffix_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2206_; 
v_xs_2185_ = lean_ctor_get(v___y_2129_, 0);
v_numCandidates_2186_ = lean_ctor_get(v___y_2129_, 1);
v_cleanSuffix_2187_ = lean_ctor_get(v___y_2129_, 2);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___y_2129_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2189_ = v___y_2129_;
v_isShared_2190_ = v_isSharedCheck_2206_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_cleanSuffix_2187_);
lean_inc(v_numCandidates_2186_);
lean_inc(v_xs_2185_);
lean_dec(v___y_2129_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2206_;
goto v_resetjp_2188_;
}
v___jp_2138_:
{
lean_object* v___x_2140_; lean_object* v_visited_2141_; lean_object* v_types_2142_; lean_object* v_subst_2143_; lean_object* v_visitedClosed_2144_; lean_object* v_hasDepLetCache_2145_; lean_object* v_numConverted_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2184_; 
v___x_2140_ = lean_st_ref_take(v___y_2130_);
v_visited_2141_ = lean_ctor_get(v___x_2140_, 0);
v_types_2142_ = lean_ctor_get(v___x_2140_, 1);
v_subst_2143_ = lean_ctor_get(v___x_2140_, 2);
v_visitedClosed_2144_ = lean_ctor_get(v___x_2140_, 3);
v_hasDepLetCache_2145_ = lean_ctor_get(v___x_2140_, 4);
v_numConverted_2146_ = lean_ctor_get(v___x_2140_, 5);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2148_ = v___x_2140_;
v_isShared_2149_ = v_isSharedCheck_2184_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_numConverted_2146_);
lean_inc(v_hasDepLetCache_2145_);
lean_inc(v_visitedClosed_2144_);
lean_inc(v_subst_2143_);
lean_inc(v_types_2142_);
lean_inc(v_visited_2141_);
lean_dec(v___x_2140_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2184_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2150_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 2, v___x_2150_);
lean_ctor_set(v___x_2148_, 1, v___x_2150_);
lean_ctor_set(v___x_2148_, 0, v___x_2150_);
v___x_2152_ = v___x_2148_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2183_, 2, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2183_, 3, v_visitedClosed_2144_);
lean_ctor_set(v_reuseFailAlloc_2183_, 4, v_hasDepLetCache_2145_);
lean_ctor_set(v_reuseFailAlloc_2183_, 5, v_numConverted_2146_);
v___x_2152_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2153_; lean_object* v_r_2154_; 
v___x_2153_ = lean_st_ref_put(v___y_2130_, v___x_2152_);
lean_inc(v___y_2136_);
lean_inc_ref(v___y_2135_);
lean_inc(v___y_2134_);
lean_inc_ref(v___y_2133_);
lean_inc(v___y_2132_);
lean_inc_ref(v___y_2131_);
lean_inc(v___y_2130_);
v_r_2154_ = lean_apply_10(v_k_2125_, v_a_2126_, v___y_2139_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, lean_box(0));
if (lean_obj_tag(v_r_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2171_; 
v_a_2155_ = lean_ctor_get(v_r_2154_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_r_2154_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2157_ = v_r_2154_;
v_isShared_2158_ = v_isSharedCheck_2171_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v_r_2154_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2171_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
lean_inc(v_a_2155_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set_tag(v___x_2157_, 1);
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
v___x_2161_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(v___y_2130_, v_visited_2141_, v_types_2142_, v_subst_2143_, v___x_2160_);
lean_dec_ref(v___x_2160_);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2168_ == 0)
{
lean_object* v_unused_2169_; 
v_unused_2169_ = lean_ctor_get(v___x_2161_, 0);
lean_dec(v_unused_2169_);
v___x_2163_ = v___x_2161_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_dec(v___x_2161_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v_a_2155_);
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2155_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
v_a_2172_ = lean_ctor_get(v_r_2154_, 0);
lean_inc(v_a_2172_);
lean_dec_ref_known(v_r_2154_, 1);
v___x_2173_ = lean_box(0);
v___x_2174_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(v___y_2130_, v_visited_2141_, v_types_2142_, v_subst_2143_, v___x_2173_);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; 
v_unused_2182_ = lean_ctor_get(v___x_2174_, 0);
lean_dec(v_unused_2182_);
v___x_2176_ = v___x_2174_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_dec(v___x_2174_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
lean_ctor_set_tag(v___x_2176_, 1);
lean_ctor_set(v___x_2176_, 0, v_a_2172_);
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2172_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
}
v_resetjp_2188_:
{
lean_object* v___x_2191_; lean_object* v___y_2193_; 
lean_inc_ref(v_a_2126_);
v___x_2191_ = l_Lean_PersistentArray_push___redArg(v_xs_2185_, v_a_2126_);
if (v_isCandidate_2128_ == 0)
{
lean_object* v___x_2204_; 
v___x_2204_ = lean_unsigned_to_nat(0u);
v___y_2193_ = v___x_2204_;
goto v___jp_2192_;
}
else
{
lean_object* v___x_2205_; 
v___x_2205_ = lean_unsigned_to_nat(1u);
v___y_2193_ = v___x_2205_;
goto v___jp_2192_;
}
v___jp_2192_:
{
lean_object* v___x_2194_; 
v___x_2194_ = lean_nat_add(v_numCandidates_2186_, v___y_2193_);
lean_dec(v_numCandidates_2186_);
if (v_tainted_2127_ == 0)
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2195_ = lean_unsigned_to_nat(1u);
v___x_2196_ = lean_nat_add(v_cleanSuffix_2187_, v___x_2195_);
lean_dec(v_cleanSuffix_2187_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 2, v___x_2196_);
lean_ctor_set(v___x_2189_, 1, v___x_2194_);
lean_ctor_set(v___x_2189_, 0, v___x_2191_);
v___x_2198_ = v___x_2189_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2199_, 2, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
v___y_2139_ = v___x_2198_;
goto v___jp_2138_;
}
}
else
{
lean_object* v___x_2200_; lean_object* v___x_2202_; 
lean_dec(v_cleanSuffix_2187_);
v___x_2200_ = lean_unsigned_to_nat(0u);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 2, v___x_2200_);
lean_ctor_set(v___x_2189_, 1, v___x_2194_);
lean_ctor_set(v___x_2189_, 0, v___x_2191_);
v___x_2202_ = v___x_2189_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2203_, 2, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
v___y_2139_ = v___x_2202_;
goto v___jp_2138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1___boxed(lean_object* v_k_2207_, lean_object* v_a_2208_, lean_object* v_tainted_2209_, lean_object* v_isCandidate_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
uint8_t v_tainted_boxed_2220_; uint8_t v_isCandidate_boxed_2221_; lean_object* v_res_2222_; 
v_tainted_boxed_2220_ = lean_unbox(v_tainted_2209_);
v_isCandidate_boxed_2221_ = lean_unbox(v_isCandidate_2210_);
v_res_2222_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1(v_k_2207_, v_a_2208_, v_tainted_boxed_2220_, v_isCandidate_boxed_2221_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg(lean_object* v___y_2223_){
_start:
{
lean_object* v___x_2225_; lean_object* v_ngen_2226_; lean_object* v_namePrefix_2227_; lean_object* v_idx_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2257_; 
v___x_2225_ = lean_st_ref_get(v___y_2223_);
v_ngen_2226_ = lean_ctor_get(v___x_2225_, 2);
lean_inc_ref(v_ngen_2226_);
lean_dec(v___x_2225_);
v_namePrefix_2227_ = lean_ctor_get(v_ngen_2226_, 0);
v_idx_2228_ = lean_ctor_get(v_ngen_2226_, 1);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_ngen_2226_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2230_ = v_ngen_2226_;
v_isShared_2231_ = v_isSharedCheck_2257_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_idx_2228_);
lean_inc(v_namePrefix_2227_);
lean_dec(v_ngen_2226_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2257_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2232_; lean_object* v_env_2233_; lean_object* v_nextMacroScope_2234_; lean_object* v_auxDeclNGen_2235_; lean_object* v_traceState_2236_; lean_object* v_cache_2237_; lean_object* v_messages_2238_; lean_object* v_infoState_2239_; lean_object* v_snapshotTasks_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2255_; 
v___x_2232_ = lean_st_ref_take(v___y_2223_);
v_env_2233_ = lean_ctor_get(v___x_2232_, 0);
v_nextMacroScope_2234_ = lean_ctor_get(v___x_2232_, 1);
v_auxDeclNGen_2235_ = lean_ctor_get(v___x_2232_, 3);
v_traceState_2236_ = lean_ctor_get(v___x_2232_, 4);
v_cache_2237_ = lean_ctor_get(v___x_2232_, 5);
v_messages_2238_ = lean_ctor_get(v___x_2232_, 6);
v_infoState_2239_ = lean_ctor_get(v___x_2232_, 7);
v_snapshotTasks_2240_ = lean_ctor_get(v___x_2232_, 8);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2255_ == 0)
{
lean_object* v_unused_2256_; 
v_unused_2256_ = lean_ctor_get(v___x_2232_, 2);
lean_dec(v_unused_2256_);
v___x_2242_ = v___x_2232_;
v_isShared_2243_ = v_isSharedCheck_2255_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_snapshotTasks_2240_);
lean_inc(v_infoState_2239_);
lean_inc(v_messages_2238_);
lean_inc(v_cache_2237_);
lean_inc(v_traceState_2236_);
lean_inc(v_auxDeclNGen_2235_);
lean_inc(v_nextMacroScope_2234_);
lean_inc(v_env_2233_);
lean_dec(v___x_2232_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2255_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v_r_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2248_; 
lean_inc(v_idx_2228_);
lean_inc(v_namePrefix_2227_);
v_r_2244_ = l_Lean_Name_num___override(v_namePrefix_2227_, v_idx_2228_);
v___x_2245_ = lean_unsigned_to_nat(1u);
v___x_2246_ = lean_nat_add(v_idx_2228_, v___x_2245_);
lean_dec(v_idx_2228_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 1, v___x_2246_);
v___x_2248_ = v___x_2230_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_namePrefix_2227_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2250_; 
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 2, v___x_2248_);
v___x_2250_ = v___x_2242_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_env_2233_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_nextMacroScope_2234_);
lean_ctor_set(v_reuseFailAlloc_2253_, 2, v___x_2248_);
lean_ctor_set(v_reuseFailAlloc_2253_, 3, v_auxDeclNGen_2235_);
lean_ctor_set(v_reuseFailAlloc_2253_, 4, v_traceState_2236_);
lean_ctor_set(v_reuseFailAlloc_2253_, 5, v_cache_2237_);
lean_ctor_set(v_reuseFailAlloc_2253_, 6, v_messages_2238_);
lean_ctor_set(v_reuseFailAlloc_2253_, 7, v_infoState_2239_);
lean_ctor_set(v_reuseFailAlloc_2253_, 8, v_snapshotTasks_2240_);
v___x_2250_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = lean_st_ref_put(v___y_2223_, v___x_2250_);
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v_r_2244_);
return v___x_2252_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg___boxed(lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg(v___y_2258_);
lean_dec(v___y_2258_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0(lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v___x_2270_; lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
v___x_2270_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg(v___y_2268_);
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2270_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2270_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0___boxed(lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0(v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(lean_object* v_n_2291_, lean_object* v_type_2292_, lean_object* v_value_x3f_2293_, uint8_t v_tainted_2294_, uint8_t v_isCandidate_2295_, lean_object* v_k_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0(v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2308_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc_n(v_a_2307_, 2);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2308_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(v_a_2307_, v_a_2300_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v_lctx_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___f_2313_; lean_object* v___y_2315_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2308_, 1);
v_lctx_2310_ = lean_ctor_get(v_a_2301_, 2);
v___x_2311_ = lean_box(v_tainted_2294_);
v___x_2312_ = lean_box(v_isCandidate_2295_);
v___f_2313_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2313_, 0, v_k_2296_);
lean_closure_set(v___f_2313_, 1, v_a_2309_);
lean_closure_set(v___f_2313_, 2, v___x_2311_);
lean_closure_set(v___f_2313_, 3, v___x_2312_);
if (lean_obj_tag(v_value_x3f_2293_) == 0)
{
uint8_t v___x_2318_; uint8_t v___x_2319_; lean_object* v___x_2320_; 
v___x_2318_ = 0;
v___x_2319_ = 0;
lean_inc_ref(v_lctx_2310_);
v___x_2320_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2310_, v_a_2307_, v_n_2291_, v_type_2292_, v___x_2318_, v___x_2319_);
v___y_2315_ = v___x_2320_;
goto v___jp_2314_;
}
else
{
lean_object* v_val_2321_; lean_object* v_fst_2322_; lean_object* v_snd_2323_; uint8_t v___x_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; 
v_val_2321_ = lean_ctor_get(v_value_x3f_2293_, 0);
lean_inc(v_val_2321_);
lean_dec_ref_known(v_value_x3f_2293_, 1);
v_fst_2322_ = lean_ctor_get(v_val_2321_, 0);
lean_inc(v_fst_2322_);
v_snd_2323_ = lean_ctor_get(v_val_2321_, 1);
lean_inc(v_snd_2323_);
lean_dec(v_val_2321_);
v___x_2324_ = 0;
v___x_2325_ = lean_unbox(v_snd_2323_);
lean_dec(v_snd_2323_);
lean_inc_ref(v_lctx_2310_);
v___x_2326_ = l_Lean_LocalContext_mkLetDecl(v_lctx_2310_, v_a_2307_, v_n_2291_, v_type_2292_, v_fst_2322_, v___x_2325_, v___x_2324_);
v___y_2315_ = v___x_2326_;
goto v___jp_2314_;
}
v___jp_2314_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___closed__0));
v___x_2317_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(v___y_2315_, v___x_2316_, v___f_2313_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
return v___x_2317_;
}
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec(v_a_2307_);
lean_dec_ref(v_k_2296_);
lean_dec(v_value_x3f_2293_);
lean_dec_ref(v_type_2292_);
lean_dec(v_n_2291_);
v_a_2327_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2308_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2308_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec_ref(v_k_2296_);
lean_dec(v_value_x3f_2293_);
lean_dec_ref(v_type_2292_);
lean_dec(v_n_2291_);
v_a_2335_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2306_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2306_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___boxed(lean_object* v_n_2343_, lean_object* v_type_2344_, lean_object* v_value_x3f_2345_, lean_object* v_tainted_2346_, lean_object* v_isCandidate_2347_, lean_object* v_k_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_){
_start:
{
uint8_t v_tainted_boxed_2358_; uint8_t v_isCandidate_boxed_2359_; lean_object* v_res_2360_; 
v_tainted_boxed_2358_ = lean_unbox(v_tainted_2346_);
v_isCandidate_boxed_2359_ = lean_unbox(v_isCandidate_2347_);
v_res_2360_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_n_2343_, v_type_2344_, v_value_x3f_2345_, v_tainted_boxed_2358_, v_isCandidate_boxed_2359_, v_k_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_);
lean_dec(v_a_2356_);
lean_dec_ref(v_a_2355_);
lean_dec(v_a_2354_);
lean_dec_ref(v_a_2353_);
lean_dec(v_a_2352_);
lean_dec_ref(v_a_2351_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder(lean_object* v_00_u03b1_2361_, lean_object* v_n_2362_, lean_object* v_type_2363_, lean_object* v_value_x3f_2364_, uint8_t v_tainted_2365_, uint8_t v_isCandidate_2366_, lean_object* v_k_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_n_2362_, v_type_2363_, v_value_x3f_2364_, v_tainted_2365_, v_isCandidate_2366_, v_k_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___boxed(lean_object* v_00_u03b1_2378_, lean_object* v_n_2379_, lean_object* v_type_2380_, lean_object* v_value_x3f_2381_, lean_object* v_tainted_2382_, lean_object* v_isCandidate_2383_, lean_object* v_k_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_){
_start:
{
uint8_t v_tainted_boxed_2394_; uint8_t v_isCandidate_boxed_2395_; lean_object* v_res_2396_; 
v_tainted_boxed_2394_ = lean_unbox(v_tainted_2382_);
v_isCandidate_boxed_2395_ = lean_unbox(v_isCandidate_2383_);
v_res_2396_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder(v_00_u03b1_2378_, v_n_2379_, v_type_2380_, v_value_x3f_2381_, v_tainted_boxed_2394_, v_isCandidate_boxed_2395_, v_k_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0(lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg(v___y_2404_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___boxed(lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0(v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0(lean_object* v_msg_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v_toApplicative_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2494_; 
v___x_2427_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0);
v___x_2428_ = l_StateRefT_x27_instMonad___redArg(v___x_2427_);
v_toApplicative_2429_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2494_ == 0)
{
lean_object* v_unused_2495_; 
v_unused_2495_ = lean_ctor_get(v___x_2428_, 1);
lean_dec(v_unused_2495_);
v___x_2431_ = v___x_2428_;
v_isShared_2432_ = v_isSharedCheck_2494_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_toApplicative_2429_);
lean_dec(v___x_2428_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2494_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v_toFunctor_2433_; lean_object* v_toSeq_2434_; lean_object* v_toSeqLeft_2435_; lean_object* v_toSeqRight_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2492_; 
v_toFunctor_2433_ = lean_ctor_get(v_toApplicative_2429_, 0);
v_toSeq_2434_ = lean_ctor_get(v_toApplicative_2429_, 2);
v_toSeqLeft_2435_ = lean_ctor_get(v_toApplicative_2429_, 3);
v_toSeqRight_2436_ = lean_ctor_get(v_toApplicative_2429_, 4);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_toApplicative_2429_);
if (v_isSharedCheck_2492_ == 0)
{
lean_object* v_unused_2493_; 
v_unused_2493_ = lean_ctor_get(v_toApplicative_2429_, 1);
lean_dec(v_unused_2493_);
v___x_2438_ = v_toApplicative_2429_;
v_isShared_2439_ = v_isSharedCheck_2492_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_toSeqRight_2436_);
lean_inc(v_toSeqLeft_2435_);
lean_inc(v_toSeq_2434_);
lean_inc(v_toFunctor_2433_);
lean_dec(v_toApplicative_2429_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2492_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___f_2440_; lean_object* v___f_2441_; lean_object* v___f_2442_; lean_object* v___f_2443_; lean_object* v___x_2444_; lean_object* v___f_2445_; lean_object* v___f_2446_; lean_object* v___f_2447_; lean_object* v___x_2449_; 
v___f_2440_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__1));
v___f_2441_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__2));
lean_inc_ref(v_toFunctor_2433_);
v___f_2442_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2442_, 0, v_toFunctor_2433_);
v___f_2443_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2443_, 0, v_toFunctor_2433_);
v___x_2444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___f_2442_);
lean_ctor_set(v___x_2444_, 1, v___f_2443_);
v___f_2445_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2445_, 0, v_toSeqRight_2436_);
v___f_2446_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2446_, 0, v_toSeqLeft_2435_);
v___f_2447_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2447_, 0, v_toSeq_2434_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 4, v___f_2445_);
lean_ctor_set(v___x_2438_, 3, v___f_2446_);
lean_ctor_set(v___x_2438_, 2, v___f_2447_);
lean_ctor_set(v___x_2438_, 1, v___f_2440_);
lean_ctor_set(v___x_2438_, 0, v___x_2444_);
v___x_2449_ = v___x_2438_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2444_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v___f_2440_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v___f_2447_);
lean_ctor_set(v_reuseFailAlloc_2491_, 3, v___f_2446_);
lean_ctor_set(v_reuseFailAlloc_2491_, 4, v___f_2445_);
v___x_2449_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2451_; 
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 1, v___f_2441_);
lean_ctor_set(v___x_2431_, 0, v___x_2449_);
v___x_2451_ = v___x_2431_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v___f_2441_);
v___x_2451_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
lean_object* v___x_2452_; lean_object* v_toApplicative_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2488_; 
v___x_2452_ = l_StateRefT_x27_instMonad___redArg(v___x_2451_);
v_toApplicative_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2488_ == 0)
{
lean_object* v_unused_2489_; 
v_unused_2489_ = lean_ctor_get(v___x_2452_, 1);
lean_dec(v_unused_2489_);
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2488_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_toApplicative_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2488_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v_toFunctor_2457_; lean_object* v_toSeq_2458_; lean_object* v_toSeqLeft_2459_; lean_object* v_toSeqRight_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2486_; 
v_toFunctor_2457_ = lean_ctor_get(v_toApplicative_2453_, 0);
v_toSeq_2458_ = lean_ctor_get(v_toApplicative_2453_, 2);
v_toSeqLeft_2459_ = lean_ctor_get(v_toApplicative_2453_, 3);
v_toSeqRight_2460_ = lean_ctor_get(v_toApplicative_2453_, 4);
v_isSharedCheck_2486_ = !lean_is_exclusive(v_toApplicative_2453_);
if (v_isSharedCheck_2486_ == 0)
{
lean_object* v_unused_2487_; 
v_unused_2487_ = lean_ctor_get(v_toApplicative_2453_, 1);
lean_dec(v_unused_2487_);
v___x_2462_ = v_toApplicative_2453_;
v_isShared_2463_ = v_isSharedCheck_2486_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_toSeqRight_2460_);
lean_inc(v_toSeqLeft_2459_);
lean_inc(v_toSeq_2458_);
lean_inc(v_toFunctor_2457_);
lean_dec(v_toApplicative_2453_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2486_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___f_2464_; lean_object* v___f_2465_; lean_object* v___f_2466_; lean_object* v___f_2467_; lean_object* v___x_2468_; lean_object* v___f_2469_; lean_object* v___f_2470_; lean_object* v___f_2471_; lean_object* v___x_2473_; 
v___f_2464_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__3));
v___f_2465_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__4));
lean_inc_ref(v_toFunctor_2457_);
v___f_2466_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2466_, 0, v_toFunctor_2457_);
v___f_2467_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2467_, 0, v_toFunctor_2457_);
v___x_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___f_2466_);
lean_ctor_set(v___x_2468_, 1, v___f_2467_);
v___f_2469_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2469_, 0, v_toSeqRight_2460_);
v___f_2470_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2470_, 0, v_toSeqLeft_2459_);
v___f_2471_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2471_, 0, v_toSeq_2458_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 4, v___f_2469_);
lean_ctor_set(v___x_2462_, 3, v___f_2470_);
lean_ctor_set(v___x_2462_, 2, v___f_2471_);
lean_ctor_set(v___x_2462_, 1, v___f_2464_);
lean_ctor_set(v___x_2462_, 0, v___x_2468_);
v___x_2473_ = v___x_2462_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2468_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v___f_2464_);
lean_ctor_set(v_reuseFailAlloc_2485_, 2, v___f_2471_);
lean_ctor_set(v_reuseFailAlloc_2485_, 3, v___f_2470_);
lean_ctor_set(v_reuseFailAlloc_2485_, 4, v___f_2469_);
v___x_2473_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2475_; 
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 1, v___f_2465_);
lean_ctor_set(v___x_2455_, 0, v___x_2473_);
v___x_2475_ = v___x_2455_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v___f_2465_);
v___x_2475_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___f_2481_; lean_object* v___x_6195__overap_2482_; lean_object* v___x_2483_; 
v___x_2476_ = l_StateRefT_x27_instMonad___redArg(v___x_2475_);
v___x_2477_ = l_ReaderT_instMonad___redArg(v___x_2476_);
v___x_2478_ = l_StateRefT_x27_instMonad___redArg(v___x_2477_);
v___x_2479_ = lean_box(0);
v___x_2480_ = l_instInhabitedOfMonad___redArg(v___x_2478_, v___x_2479_);
v___f_2481_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2481_, 0, v___x_2480_);
v___x_6195__overap_2482_ = lean_panic_fn_borrowed(v___f_2481_, v_msg_2417_);
lean_dec_ref(v___f_2481_);
lean_inc(v___y_2425_);
lean_inc_ref(v___y_2424_);
lean_inc(v___y_2423_);
lean_inc_ref(v___y_2422_);
lean_inc(v___y_2421_);
lean_inc_ref(v___y_2420_);
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
v___x_2483_ = lean_apply_9(v___x_6195__overap_2482_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, lean_box(0));
return v___x_2483_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0___boxed(lean_object* v_msg_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0(v_msg_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0___boxed(lean_object* v_body_2507_, lean_object* v_body_2508_, lean_object* v_x_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0(v_body_2507_, v_body_2508_, v_x_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec_ref(v_x_2509_);
return v_res_2519_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__1(void){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2521_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_2522_ = lean_unsigned_to_nat(42u);
v___x_2523_ = lean_unsigned_to_nat(340u);
v___x_2524_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__0));
v___x_2525_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0));
v___x_2526_ = l_mkPanicMessageWithDecl(v___x_2525_, v___x_2524_, v___x_2523_, v___x_2522_, v___x_2521_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(lean_object* v_e_2527_, lean_object* v_expected_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_){
_start:
{
if (lean_obj_tag(v_e_2527_) == 6)
{
lean_object* v_binderName_2538_; lean_object* v_binderType_2539_; lean_object* v_body_2540_; lean_object* v___x_2541_; 
v_binderName_2538_ = lean_ctor_get(v_e_2527_, 0);
lean_inc(v_binderName_2538_);
v_binderType_2539_ = lean_ctor_get(v_e_2527_, 1);
lean_inc_ref(v_binderType_2539_);
v_body_2540_ = lean_ctor_get(v_e_2527_, 2);
lean_inc_ref(v_body_2540_);
lean_dec_ref_known(v_e_2527_, 3);
v___x_2541_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_expected_2528_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___x_2541_, 1);
if (lean_obj_tag(v_a_2542_) == 7)
{
lean_object* v_binderType_2543_; lean_object* v_body_2544_; lean_object* v___x_2545_; 
v_binderType_2543_ = lean_ctor_get(v_a_2542_, 1);
lean_inc_ref(v_binderType_2543_);
v_body_2544_ = lean_ctor_get(v_a_2542_, 2);
lean_inc_ref(v_body_2544_);
lean_dec_ref_known(v_a_2542_, 3);
lean_inc_ref(v_binderType_2539_);
v___x_2545_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_binderType_2539_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2547_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc_n(v_a_2546_, 2);
lean_dec_ref_known(v___x_2545_, 1);
v___x_2547_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_a_2546_, v_binderType_2543_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_cleanSuffix_2548_; lean_object* v___f_2549_; lean_object* v___x_2550_; uint8_t v___y_2552_; lean_object* v___x_2555_; uint8_t v___x_2556_; 
lean_dec_ref_known(v___x_2547_, 1);
v_cleanSuffix_2548_ = lean_ctor_get(v_a_2529_, 2);
v___f_2549_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0___boxed), 12, 2);
lean_closure_set(v___f_2549_, 0, v_body_2544_);
lean_closure_set(v___f_2549_, 1, v_body_2540_);
v___x_2550_ = lean_box(0);
v___x_2555_ = l_Lean_Expr_looseBVarRange(v_binderType_2539_);
lean_dec_ref(v_binderType_2539_);
v___x_2556_ = lean_nat_dec_le(v___x_2555_, v_cleanSuffix_2548_);
lean_dec(v___x_2555_);
if (v___x_2556_ == 0)
{
uint8_t v___x_2557_; 
v___x_2557_ = 1;
v___y_2552_ = v___x_2557_;
goto v___jp_2551_;
}
else
{
uint8_t v___x_2558_; 
v___x_2558_ = 0;
v___y_2552_ = v___x_2558_;
goto v___jp_2551_;
}
v___jp_2551_:
{
uint8_t v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = 0;
v___x_2554_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_binderName_2538_, v_a_2546_, v___x_2550_, v___y_2552_, v___x_2553_, v___f_2549_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
return v___x_2554_;
}
}
else
{
lean_dec(v_a_2546_);
lean_dec_ref(v_body_2544_);
lean_dec_ref(v_body_2540_);
lean_dec_ref(v_binderType_2539_);
lean_dec(v_binderName_2538_);
return v___x_2547_;
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec_ref(v_body_2544_);
lean_dec_ref(v_binderType_2543_);
lean_dec_ref(v_body_2540_);
lean_dec_ref(v_binderType_2539_);
lean_dec(v_binderName_2538_);
v_a_2559_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2545_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2545_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
else
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
lean_dec(v_a_2542_);
lean_dec_ref(v_body_2540_);
lean_dec_ref(v_binderType_2539_);
lean_dec(v_binderName_2538_);
v___x_2567_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__1);
v___x_2568_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0(v___x_2567_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
return v___x_2568_;
}
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec_ref(v_body_2540_);
lean_dec_ref(v_binderType_2539_);
lean_dec(v_binderName_2538_);
v_a_2569_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2541_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2541_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
else
{
lean_object* v___x_2577_; 
v___x_2577_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_e_2527_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2579_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_a_2578_);
lean_dec_ref_known(v___x_2577_, 1);
v___x_2579_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_a_2578_, v_expected_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
return v___x_2579_;
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
lean_dec_ref(v_expected_2528_);
v_a_2580_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2577_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2577_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0(lean_object* v_body_2588_, lean_object* v_body_2589_, lean_object* v_x_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
uint8_t v___x_2600_; 
v___x_2600_ = l_Lean_Expr_hasLooseBVars(v_body_2588_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; 
v___x_2601_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_body_2589_, v_body_2588_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
return v___x_2601_;
}
else
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = lean_expr_instantiate1(v_body_2588_, v_x_2590_);
lean_dec_ref(v_body_2588_);
v___x_2603_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2602_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2605_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___x_2603_, 1);
v___x_2605_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_body_2589_, v_a_2604_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
return v___x_2605_;
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec_ref(v_body_2589_);
v_a_2606_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2603_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2603_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___boxed(lean_object* v_e_2614_, lean_object* v_expected_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_e_2614_, v_expected_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_);
lean_dec(v_a_2623_);
lean_dec_ref(v_a_2622_);
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec(v_a_2619_);
lean_dec_ref(v_a_2618_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(lean_object* v_t_2626_, lean_object* v_tf_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_){
_start:
{
uint8_t v___y_2638_; lean_object* v_numCandidates_2657_; lean_object* v_cleanSuffix_2658_; lean_object* v___x_2659_; uint8_t v___x_2660_; 
v_numCandidates_2657_ = lean_ctor_get(v_a_2628_, 1);
v_cleanSuffix_2658_ = lean_ctor_get(v_a_2628_, 2);
v___x_2659_ = lean_unsigned_to_nat(0u);
v___x_2660_ = lean_nat_dec_lt(v___x_2659_, v_numCandidates_2657_);
if (v___x_2660_ == 0)
{
v___y_2638_ = v___x_2660_;
goto v___jp_2637_;
}
else
{
lean_object* v___x_2661_; uint8_t v___x_2662_; 
v___x_2661_ = l_Lean_Expr_looseBVarRange(v_t_2626_);
v___x_2662_ = lean_nat_dec_le(v___x_2661_, v_cleanSuffix_2658_);
lean_dec(v___x_2661_);
if (v___x_2662_ == 0)
{
v___y_2638_ = v___x_2660_;
goto v___jp_2637_;
}
else
{
lean_dec_ref(v_tf_2627_);
goto v___jp_2634_;
}
}
v___jp_2634_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2635_ = lean_box(0);
v___x_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
return v___x_2636_;
}
v___jp_2637_:
{
if (v___y_2638_ == 0)
{
lean_dec_ref(v_tf_2627_);
goto v___jp_2634_;
}
else
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lean_Meta_getLevel(v_tf_2627_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2647_; 
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2647_ == 0)
{
lean_object* v_unused_2648_; 
v_unused_2648_ = lean_ctor_get(v___x_2639_, 0);
lean_dec(v_unused_2648_);
v___x_2641_ = v___x_2639_;
v_isShared_2642_ = v_isSharedCheck_2647_;
goto v_resetjp_2640_;
}
else
{
lean_dec(v___x_2639_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2647_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2643_ = lean_box(0);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v___x_2643_);
v___x_2645_ = v___x_2641_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
v_a_2649_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2639_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2639_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg___boxed(lean_object* v_t_2663_, lean_object* v_tf_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_t_2663_, v_tf_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2668_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
lean_dec_ref(v_a_2665_);
lean_dec_ref(v_t_2663_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain(lean_object* v_t_2672_, lean_object* v_tf_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
lean_object* v___x_2683_; 
v___x_2683_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_t_2672_, v_tf_2673_, v_a_2674_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___boxed(lean_object* v_t_2684_, lean_object* v_tf_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain(v_t_2684_, v_tf_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec_ref(v_t_2684_);
return v_res_2695_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1(void){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2697_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_2698_ = lean_unsigned_to_nat(35u);
v___x_2699_ = lean_unsigned_to_nat(322u);
v___x_2700_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__0));
v___x_2701_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0));
v___x_2702_ = l_mkPanicMessageWithDecl(v___x_2701_, v___x_2700_, v___x_2699_, v___x_2698_, v___x_2697_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp(lean_object* v_f_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_f_2703_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2716_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_a_2715_);
lean_dec_ref_known(v___x_2714_, 1);
v___x_2716_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_a_2715_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2744_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2719_ = v___x_2716_;
v_isShared_2720_ = v_isSharedCheck_2744_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2716_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2744_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
if (lean_obj_tag(v_a_2717_) == 7)
{
lean_object* v_binderType_2721_; uint8_t v___x_2736_; 
v_binderType_2721_ = lean_ctor_get(v_a_2717_, 1);
lean_inc_ref(v_binderType_2721_);
lean_dec_ref_known(v_a_2717_, 3);
v___x_2736_ = l_Lean_Expr_hasLooseBVars(v_a_2704_);
if (v___x_2736_ == 0)
{
uint8_t v___x_2737_; 
v___x_2737_ = l_Lean_Expr_hasFVar(v_binderType_2721_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; lean_object* v___x_2740_; 
lean_dec_ref(v_binderType_2721_);
lean_dec_ref(v_a_2704_);
v___x_2738_ = lean_box(0);
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v___x_2738_);
v___x_2740_ = v___x_2719_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2738_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
else
{
lean_del_object(v___x_2719_);
goto v___jp_2722_;
}
}
else
{
lean_del_object(v___x_2719_);
goto v___jp_2722_;
}
v___jp_2722_:
{
uint8_t v___x_2723_; 
v___x_2723_ = l_Lean_Expr_isLambda(v_a_2704_);
if (v___x_2723_ == 0)
{
lean_object* v___x_2724_; 
v___x_2724_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v_a_2725_; lean_object* v___x_2726_; 
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
lean_inc(v_a_2725_);
lean_dec_ref_known(v___x_2724_, 1);
v___x_2726_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_a_2725_, v_binderType_2721_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_);
return v___x_2726_;
}
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
lean_dec_ref(v_binderType_2721_);
v_a_2727_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___x_2724_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2724_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
else
{
lean_object* v___x_2735_; 
v___x_2735_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_a_2704_, v_binderType_2721_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_);
return v___x_2735_;
}
}
}
else
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
lean_del_object(v___x_2719_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2704_);
v___x_2742_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1);
v___x_2743_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0(v___x_2742_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_);
return v___x_2743_;
}
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_dec_ref(v_a_2704_);
v_a_2745_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2716_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2716_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
lean_dec_ref(v_a_2704_);
v_a_2753_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2714_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2714_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___boxed(lean_object* v_f_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp(v_f_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
lean_dec(v_a_2770_);
lean_dec_ref(v_a_2769_);
lean_dec(v_a_2768_);
lean_dec_ref(v_a_2767_);
lean_dec(v_a_2766_);
lean_dec_ref(v_a_2765_);
lean_dec(v_a_2764_);
lean_dec_ref(v_a_2763_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(lean_object* v_x_2773_, uint8_t v_bi_2774_, lean_object* v_t_2775_, lean_object* v_b_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v___y_2785_; lean_object* v___x_2788_; uint8_t v_debug_2789_; 
v___x_2788_ = lean_st_ref_get(v___y_2778_);
v_debug_2789_ = lean_ctor_get_uint8(v___x_2788_, sizeof(void*)*11);
lean_dec(v___x_2788_);
if (v_debug_2789_ == 0)
{
v___y_2785_ = v___y_2778_;
goto v___jp_2784_;
}
else
{
lean_object* v___x_2790_; 
v___x_2790_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2775_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v___x_2791_; 
lean_dec_ref_known(v___x_2790_, 1);
v___x_2791_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_dec_ref_known(v___x_2791_, 1);
v___y_2785_ = v___y_2778_;
goto v___jp_2784_;
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_dec_ref(v_b_2776_);
lean_dec_ref(v_t_2775_);
lean_dec(v_x_2773_);
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2791_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec_ref(v_b_2776_);
lean_dec_ref(v_t_2775_);
lean_dec(v_x_2773_);
v_a_2800_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2790_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2790_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
v___jp_2784_:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = l_Lean_Expr_lam___override(v_x_2773_, v_t_2775_, v_b_2776_, v_bi_2774_);
v___x_2787_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2786_, v___y_2785_);
return v___x_2787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg___boxed(lean_object* v_x_2808_, lean_object* v_bi_2809_, lean_object* v_t_2810_, lean_object* v_b_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
uint8_t v_bi_boxed_2819_; lean_object* v_res_2820_; 
v_bi_boxed_2819_ = lean_unbox(v_bi_2809_);
v_res_2820_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(v_x_2808_, v_bi_boxed_2819_, v_t_2810_, v_b_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(lean_object* v_x_2821_, lean_object* v_t_2822_, lean_object* v_v_2823_, lean_object* v_b_2824_, uint8_t v_nondep_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v___y_2834_; lean_object* v___x_2837_; uint8_t v_debug_2838_; 
v___x_2837_ = lean_st_ref_get(v___y_2827_);
v_debug_2838_ = lean_ctor_get_uint8(v___x_2837_, sizeof(void*)*11);
lean_dec(v___x_2837_);
if (v_debug_2838_ == 0)
{
v___y_2834_ = v___y_2827_;
goto v___jp_2833_;
}
else
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2822_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v___x_2840_; 
lean_dec_ref_known(v___x_2839_, 1);
v___x_2840_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_v_2823_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v___x_2841_; 
lean_dec_ref_known(v___x_2840_, 1);
v___x_2841_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2824_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_dec_ref_known(v___x_2841_, 1);
v___y_2834_ = v___y_2827_;
goto v___jp_2833_;
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_dec_ref(v_b_2824_);
lean_dec_ref(v_v_2823_);
lean_dec_ref(v_t_2822_);
lean_dec(v_x_2821_);
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2841_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2841_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_dec_ref(v_b_2824_);
lean_dec_ref(v_v_2823_);
lean_dec_ref(v_t_2822_);
lean_dec(v_x_2821_);
v_a_2850_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2840_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2840_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec_ref(v_b_2824_);
lean_dec_ref(v_v_2823_);
lean_dec_ref(v_t_2822_);
lean_dec(v_x_2821_);
v_a_2858_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2839_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2839_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
v___jp_2833_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = l_Lean_Expr_letE___override(v_x_2821_, v_t_2822_, v_v_2823_, v_b_2824_, v_nondep_2825_);
v___x_2836_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2835_, v___y_2834_);
return v___x_2836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg___boxed(lean_object* v_x_2866_, lean_object* v_t_2867_, lean_object* v_v_2868_, lean_object* v_b_2869_, lean_object* v_nondep_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
uint8_t v_nondep_boxed_2878_; lean_object* v_res_2879_; 
v_nondep_boxed_2878_ = lean_unbox(v_nondep_2870_);
v_res_2879_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_x_2866_, v_t_2867_, v_v_2868_, v_b_2869_, v_nondep_boxed_2878_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
return v_res_2879_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(lean_object* v_k_2880_, lean_object* v_t_2881_){
_start:
{
if (lean_obj_tag(v_t_2881_) == 0)
{
lean_object* v_k_2882_; lean_object* v_l_2883_; lean_object* v_r_2884_; uint8_t v___x_2885_; 
v_k_2882_ = lean_ctor_get(v_t_2881_, 1);
v_l_2883_ = lean_ctor_get(v_t_2881_, 3);
v_r_2884_ = lean_ctor_get(v_t_2881_, 4);
v___x_2885_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2880_, v_k_2882_);
switch(v___x_2885_)
{
case 0:
{
v_t_2881_ = v_l_2883_;
goto _start;
}
case 1:
{
uint8_t v___x_2887_; 
v___x_2887_ = 1;
return v___x_2887_;
}
default: 
{
v_t_2881_ = v_r_2884_;
goto _start;
}
}
}
else
{
uint8_t v___x_2889_; 
v___x_2889_ = 0;
return v___x_2889_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg___boxed(lean_object* v_k_2890_, lean_object* v_t_2891_){
_start:
{
uint8_t v_res_2892_; lean_object* v_r_2893_; 
v_res_2892_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(v_k_2890_, v_t_2891_);
lean_dec(v_t_2891_);
lean_dec(v_k_2890_);
v_r_2893_ = lean_box(v_res_2892_);
return v_r_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(lean_object* v_x_2894_, uint8_t v_bi_2895_, lean_object* v_t_2896_, lean_object* v_b_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v___y_2906_; lean_object* v___x_2909_; uint8_t v_debug_2910_; 
v___x_2909_ = lean_st_ref_get(v___y_2899_);
v_debug_2910_ = lean_ctor_get_uint8(v___x_2909_, sizeof(void*)*11);
lean_dec(v___x_2909_);
if (v_debug_2910_ == 0)
{
v___y_2906_ = v___y_2899_;
goto v___jp_2905_;
}
else
{
lean_object* v___x_2911_; 
v___x_2911_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2896_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v___x_2912_; 
lean_dec_ref_known(v___x_2911_, 1);
v___x_2912_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_dec_ref_known(v___x_2912_, 1);
v___y_2906_ = v___y_2899_;
goto v___jp_2905_;
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec_ref(v_b_2897_);
lean_dec_ref(v_t_2896_);
lean_dec(v_x_2894_);
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2912_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2912_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec_ref(v_b_2897_);
lean_dec_ref(v_t_2896_);
lean_dec(v_x_2894_);
v_a_2921_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2911_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2911_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
v___jp_2905_:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2907_ = l_Lean_Expr_forallE___override(v_x_2894_, v_t_2896_, v_b_2897_, v_bi_2895_);
v___x_2908_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2907_, v___y_2906_);
return v___x_2908_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg___boxed(lean_object* v_x_2929_, lean_object* v_bi_2930_, lean_object* v_t_2931_, lean_object* v_b_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
uint8_t v_bi_boxed_2940_; lean_object* v_res_2941_; 
v_bi_boxed_2940_ = lean_unbox(v_bi_2930_);
v_res_2941_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(v_x_2929_, v_bi_boxed_2940_, v_t_2931_, v_b_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(lean_object* v_d_2942_, lean_object* v_e_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
lean_object* v___y_2952_; lean_object* v___x_2955_; uint8_t v_debug_2956_; 
v___x_2955_ = lean_st_ref_get(v___y_2945_);
v_debug_2956_ = lean_ctor_get_uint8(v___x_2955_, sizeof(void*)*11);
lean_dec(v___x_2955_);
if (v_debug_2956_ == 0)
{
v___y_2952_ = v___y_2945_;
goto v___jp_2951_;
}
else
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_dec_ref_known(v___x_2957_, 1);
v___y_2952_ = v___y_2945_;
goto v___jp_2951_;
}
else
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
lean_dec_ref(v_e_2943_);
lean_dec(v_d_2942_);
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2957_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2957_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
v___jp_2951_:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = l_Lean_Expr_mdata___override(v_d_2942_, v_e_2943_);
v___x_2954_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2953_, v___y_2952_);
return v___x_2954_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg___boxed(lean_object* v_d_2966_, lean_object* v_e_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(v_d_2966_, v_e_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(lean_object* v_structName_2976_, lean_object* v_idx_2977_, lean_object* v_struct_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
lean_object* v___y_2987_; lean_object* v___x_2990_; uint8_t v_debug_2991_; 
v___x_2990_ = lean_st_ref_get(v___y_2980_);
v_debug_2991_ = lean_ctor_get_uint8(v___x_2990_, sizeof(void*)*11);
lean_dec(v___x_2990_);
if (v_debug_2991_ == 0)
{
v___y_2987_ = v___y_2980_;
goto v___jp_2986_;
}
else
{
lean_object* v___x_2992_; 
v___x_2992_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_struct_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_dec_ref_known(v___x_2992_, 1);
v___y_2987_ = v___y_2980_;
goto v___jp_2986_;
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_dec_ref(v_struct_2978_);
lean_dec(v_idx_2977_);
lean_dec(v_structName_2976_);
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2992_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2992_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
v___jp_2986_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = l_Lean_Expr_proj___override(v_structName_2976_, v_idx_2977_, v_struct_2978_);
v___x_2989_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2988_, v___y_2987_);
return v___x_2989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg___boxed(lean_object* v_structName_3001_, lean_object* v_idx_3002_, lean_object* v_struct_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(v_structName_3001_, v_idx_3002_, v_struct_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(lean_object* v_f_3012_, lean_object* v_a_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v___y_3022_; lean_object* v___x_3025_; uint8_t v_debug_3026_; 
v___x_3025_ = lean_st_ref_get(v___y_3015_);
v_debug_3026_ = lean_ctor_get_uint8(v___x_3025_, sizeof(void*)*11);
lean_dec(v___x_3025_);
if (v_debug_3026_ == 0)
{
v___y_3022_ = v___y_3015_;
goto v___jp_3021_;
}
else
{
lean_object* v___x_3027_; 
v___x_3027_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_3012_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v___x_3028_; 
lean_dec_ref_known(v___x_3027_, 1);
v___x_3028_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_dec_ref_known(v___x_3028_, 1);
v___y_3022_ = v___y_3015_;
goto v___jp_3021_;
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_dec_ref(v_a_3013_);
lean_dec_ref(v_f_3012_);
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec_ref(v_a_3013_);
lean_dec_ref(v_f_3012_);
v_a_3037_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3027_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3027_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
v___jp_3021_:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = l_Lean_Expr_app___override(v_f_3012_, v_a_3013_);
v___x_3024_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_3023_, v___y_3022_);
return v___x_3024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg___boxed(lean_object* v_f_3045_, lean_object* v_a_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(v_f_3045_, v_a_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(lean_object* v_a_3055_, lean_object* v_visited_3056_, lean_object* v_types_3057_, lean_object* v_subst_3058_, lean_object* v_a_x3f_3059_){
_start:
{
lean_object* v___x_3061_; lean_object* v_visitedClosed_3062_; lean_object* v_hasDepLetCache_3063_; lean_object* v_numConverted_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3074_; 
v___x_3061_ = lean_st_ref_take(v_a_3055_);
v_visitedClosed_3062_ = lean_ctor_get(v___x_3061_, 3);
v_hasDepLetCache_3063_ = lean_ctor_get(v___x_3061_, 4);
v_numConverted_3064_ = lean_ctor_get(v___x_3061_, 5);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3074_ == 0)
{
lean_object* v_unused_3075_; lean_object* v_unused_3076_; lean_object* v_unused_3077_; 
v_unused_3075_ = lean_ctor_get(v___x_3061_, 2);
lean_dec(v_unused_3075_);
v_unused_3076_ = lean_ctor_get(v___x_3061_, 1);
lean_dec(v_unused_3076_);
v_unused_3077_ = lean_ctor_get(v___x_3061_, 0);
lean_dec(v_unused_3077_);
v___x_3066_ = v___x_3061_;
v_isShared_3067_ = v_isSharedCheck_3074_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_numConverted_3064_);
lean_inc(v_hasDepLetCache_3063_);
lean_inc(v_visitedClosed_3062_);
lean_dec(v___x_3061_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3074_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 2, v_subst_3058_);
lean_ctor_set(v___x_3066_, 1, v_types_3057_);
lean_ctor_set(v___x_3066_, 0, v_visited_3056_);
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_visited_3056_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v_types_3057_);
lean_ctor_set(v_reuseFailAlloc_3073_, 2, v_subst_3058_);
lean_ctor_set(v_reuseFailAlloc_3073_, 3, v_visitedClosed_3062_);
lean_ctor_set(v_reuseFailAlloc_3073_, 4, v_hasDepLetCache_3063_);
lean_ctor_set(v_reuseFailAlloc_3073_, 5, v_numConverted_3064_);
v___x_3069_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = lean_st_ref_put(v_a_3055_, v___x_3069_);
v___x_3071_ = lean_box(0);
v___x_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
return v___x_3072_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0___boxed(lean_object* v_a_3078_, lean_object* v_visited_3079_, lean_object* v_types_3080_, lean_object* v_subst_3081_, lean_object* v_a_x3f_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(v_a_3078_, v_visited_3079_, v_types_3080_, v_subst_3081_, v_a_x3f_3082_);
lean_dec(v_a_x3f_3082_);
lean_dec(v_a_3078_);
return v_res_3084_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0(void){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3085_ = lean_unsigned_to_nat(32u);
v___x_3086_ = lean_mk_empty_array_with_capacity(v___x_3085_);
v___x_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
return v___x_3087_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1(void){
_start:
{
size_t v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3088_ = ((size_t)5ULL);
v___x_3089_ = lean_unsigned_to_nat(0u);
v___x_3090_ = lean_unsigned_to_nat(32u);
v___x_3091_ = lean_mk_empty_array_with_capacity(v___x_3090_);
v___x_3092_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0);
v___x_3093_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3093_, 0, v___x_3092_);
lean_ctor_set(v___x_3093_, 1, v___x_3091_);
lean_ctor_set(v___x_3093_, 2, v___x_3089_);
lean_ctor_set(v___x_3093_, 3, v___x_3089_);
lean_ctor_set_usize(v___x_3093_, 4, v___x_3088_);
return v___x_3093_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2(void){
_start:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3094_ = lean_unsigned_to_nat(0u);
v___x_3095_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1);
v___x_3096_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
lean_ctor_set(v___x_3096_, 1, v___x_3094_);
lean_ctor_set(v___x_3096_, 2, v___x_3094_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0___boxed(lean_object* v_body_3097_, lean_object* v_binderName_3098_, lean_object* v_binderInfo_3099_, lean_object* v_a_3100_, lean_object* v_e_3101_, lean_object* v_binderType_3102_, lean_object* v_x_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
uint8_t v_binderInfo_82333__boxed_3113_; lean_object* v_res_3114_; 
v_binderInfo_82333__boxed_3113_ = lean_unbox(v_binderInfo_3099_);
v_res_3114_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0(v_body_3097_, v_binderName_3098_, v_binderInfo_82333__boxed_3113_, v_a_3100_, v_e_3101_, v_binderType_3102_, v_x_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec_ref(v_x_3103_);
lean_dec_ref(v_binderType_3102_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0(lean_object* v_body_3115_, lean_object* v_binderName_3116_, uint8_t v_binderInfo_3117_, lean_object* v_a_3118_, lean_object* v_e_3119_, lean_object* v_binderType_3120_, lean_object* v_x_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v___x_3131_; 
lean_inc_ref(v_body_3115_);
v___x_3131_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(v_body_3115_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3148_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3134_ = v___x_3131_;
v_isShared_3135_ = v_isSharedCheck_3148_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3131_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3148_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
uint8_t v___y_3137_; size_t v___x_3142_; size_t v___x_3143_; uint8_t v___x_3144_; 
v___x_3142_ = lean_ptr_addr(v_binderType_3120_);
v___x_3143_ = lean_ptr_addr(v_a_3118_);
v___x_3144_ = lean_usize_dec_eq(v___x_3142_, v___x_3143_);
if (v___x_3144_ == 0)
{
lean_dec_ref(v_body_3115_);
v___y_3137_ = v___x_3144_;
goto v___jp_3136_;
}
else
{
size_t v___x_3145_; size_t v___x_3146_; uint8_t v___x_3147_; 
v___x_3145_ = lean_ptr_addr(v_body_3115_);
lean_dec_ref(v_body_3115_);
v___x_3146_ = lean_ptr_addr(v_a_3132_);
v___x_3147_ = lean_usize_dec_eq(v___x_3145_, v___x_3146_);
v___y_3137_ = v___x_3147_;
goto v___jp_3136_;
}
v___jp_3136_:
{
if (v___y_3137_ == 0)
{
lean_object* v___x_3138_; 
lean_del_object(v___x_3134_);
lean_dec_ref(v_e_3119_);
v___x_3138_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(v_binderName_3116_, v_binderInfo_3117_, v_a_3118_, v_a_3132_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
return v___x_3138_;
}
else
{
lean_object* v___x_3140_; 
lean_dec(v_a_3132_);
lean_dec_ref(v_a_3118_);
lean_dec(v_binderName_3116_);
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 0, v_e_3119_);
v___x_3140_ = v___x_3134_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_e_3119_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3119_);
lean_dec_ref(v_a_3118_);
lean_dec(v_binderName_3116_);
lean_dec_ref(v_body_3115_);
return v___x_3131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0___boxed(lean_object* v_body_3149_, lean_object* v_binderName_3150_, lean_object* v_binderInfo_3151_, lean_object* v_a_3152_, lean_object* v_e_3153_, lean_object* v_binderType_3154_, lean_object* v_x_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
uint8_t v_binderInfo_82361__boxed_3165_; lean_object* v_res_3166_; 
v_binderInfo_82361__boxed_3165_ = lean_unbox(v_binderInfo_3151_);
v_res_3166_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0(v_body_3149_, v_binderName_3150_, v_binderInfo_82361__boxed_3165_, v_a_3152_, v_e_3153_, v_binderType_3154_, v_x_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec_ref(v_x_3155_);
lean_dec_ref(v_binderType_3154_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(lean_object* v_e_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_){
_start:
{
if (lean_obj_tag(v_e_3167_) == 7)
{
lean_object* v_binderName_3177_; lean_object* v_binderType_3178_; lean_object* v_body_3179_; uint8_t v_binderInfo_3180_; lean_object* v___x_3181_; 
v_binderName_3177_ = lean_ctor_get(v_e_3167_, 0);
lean_inc(v_binderName_3177_);
v_binderType_3178_ = lean_ctor_get(v_e_3167_, 1);
lean_inc_ref_n(v_binderType_3178_, 2);
v_body_3179_ = lean_ctor_get(v_e_3167_, 2);
lean_inc_ref(v_body_3179_);
v_binderInfo_3180_ = lean_ctor_get_uint8(v_e_3167_, sizeof(void*)*3 + 8);
v___x_3181_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_binderType_3178_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_a_3182_; lean_object* v___x_3183_; 
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc_n(v_a_3182_, 2);
lean_dec_ref_known(v___x_3181_, 1);
v___x_3183_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3182_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; lean_object* v___x_3185_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
lean_inc_n(v_a_3184_, 2);
lean_dec_ref_known(v___x_3183_, 1);
v___x_3185_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_binderType_3178_, v_a_3184_, v_a_3168_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_cleanSuffix_3186_; lean_object* v___x_3187_; lean_object* v___f_3188_; lean_object* v___x_3189_; uint8_t v___y_3191_; lean_object* v___x_3194_; uint8_t v___x_3195_; 
lean_dec_ref_known(v___x_3185_, 1);
v_cleanSuffix_3186_ = lean_ctor_get(v_a_3168_, 2);
v___x_3187_ = lean_box(v_binderInfo_3180_);
lean_inc_ref(v_binderType_3178_);
lean_inc(v_binderName_3177_);
v___f_3188_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0___boxed), 16, 6);
lean_closure_set(v___f_3188_, 0, v_body_3179_);
lean_closure_set(v___f_3188_, 1, v_binderName_3177_);
lean_closure_set(v___f_3188_, 2, v___x_3187_);
lean_closure_set(v___f_3188_, 3, v_a_3182_);
lean_closure_set(v___f_3188_, 4, v_e_3167_);
lean_closure_set(v___f_3188_, 5, v_binderType_3178_);
v___x_3189_ = lean_box(0);
v___x_3194_ = l_Lean_Expr_looseBVarRange(v_binderType_3178_);
lean_dec_ref(v_binderType_3178_);
v___x_3195_ = lean_nat_dec_le(v___x_3194_, v_cleanSuffix_3186_);
lean_dec(v___x_3194_);
if (v___x_3195_ == 0)
{
uint8_t v___x_3196_; 
v___x_3196_ = 1;
v___y_3191_ = v___x_3196_;
goto v___jp_3190_;
}
else
{
uint8_t v___x_3197_; 
v___x_3197_ = 0;
v___y_3191_ = v___x_3197_;
goto v___jp_3190_;
}
v___jp_3190_:
{
uint8_t v___x_3192_; lean_object* v___x_3193_; 
v___x_3192_ = 0;
v___x_3193_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_binderName_3177_, v_a_3184_, v___x_3189_, v___y_3191_, v___x_3192_, v___f_3188_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_);
return v___x_3193_;
}
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_dec(v_a_3184_);
lean_dec(v_a_3182_);
lean_dec_ref(v_body_3179_);
lean_dec_ref(v_binderType_3178_);
lean_dec(v_binderName_3177_);
lean_dec_ref_known(v_e_3167_, 3);
v_a_3198_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3185_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3185_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
else
{
lean_dec(v_a_3182_);
lean_dec_ref(v_body_3179_);
lean_dec_ref(v_binderType_3178_);
lean_dec(v_binderName_3177_);
lean_dec_ref_known(v_e_3167_, 3);
return v___x_3183_;
}
}
else
{
lean_dec_ref(v_body_3179_);
lean_dec_ref(v_binderType_3178_);
lean_dec(v_binderName_3177_);
lean_dec_ref_known(v_e_3167_, 3);
return v___x_3181_;
}
}
else
{
lean_object* v___x_3206_; 
lean_inc_ref(v_e_3167_);
v___x_3206_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_e_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v_a_3207_; uint8_t v___y_3209_; lean_object* v_numCandidates_3229_; lean_object* v_cleanSuffix_3230_; lean_object* v___x_3231_; uint8_t v___x_3232_; 
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
lean_inc(v_a_3207_);
v_numCandidates_3229_ = lean_ctor_get(v_a_3168_, 1);
v_cleanSuffix_3230_ = lean_ctor_get(v_a_3168_, 2);
v___x_3231_ = lean_unsigned_to_nat(0u);
v___x_3232_ = lean_nat_dec_lt(v___x_3231_, v_numCandidates_3229_);
if (v___x_3232_ == 0)
{
lean_dec_ref(v_e_3167_);
v___y_3209_ = v___x_3232_;
goto v___jp_3208_;
}
else
{
lean_object* v___x_3233_; uint8_t v___x_3234_; 
v___x_3233_ = l_Lean_Expr_looseBVarRange(v_e_3167_);
lean_dec_ref(v_e_3167_);
v___x_3234_ = lean_nat_dec_le(v___x_3233_, v_cleanSuffix_3230_);
lean_dec(v___x_3233_);
if (v___x_3234_ == 0)
{
v___y_3209_ = v___x_3232_;
goto v___jp_3208_;
}
else
{
lean_dec(v_a_3207_);
return v___x_3206_;
}
}
v___jp_3208_:
{
if (v___y_3209_ == 0)
{
lean_dec(v_a_3207_);
return v___x_3206_;
}
else
{
lean_object* v___x_3210_; 
lean_dec_ref_known(v___x_3206_, 1);
lean_inc(v_a_3207_);
v___x_3210_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3207_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v___x_3212_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
lean_dec_ref_known(v___x_3210_, 1);
v___x_3212_ = l_Lean_Meta_getLevel(v_a_3211_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3219_ == 0)
{
lean_object* v_unused_3220_; 
v_unused_3220_ = lean_ctor_get(v___x_3212_, 0);
lean_dec(v_unused_3220_);
v___x_3214_ = v___x_3212_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_dec(v___x_3212_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3217_; 
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 0, v_a_3207_);
v___x_3217_ = v___x_3214_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3207_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_dec(v_a_3207_);
v_a_3221_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3212_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3212_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
else
{
lean_dec(v_a_3207_);
return v___x_3210_;
}
}
}
}
else
{
lean_dec_ref(v_e_3167_);
return v___x_3206_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1(lean_object* v_body_3235_, lean_object* v_declName_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, uint8_t v_nondep_3239_, lean_object* v_e_3240_, lean_object* v_type_3241_, lean_object* v_value_3242_, uint8_t v___y_3243_, lean_object* v_x_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
lean_object* v___x_3254_; 
lean_inc_ref(v_body_3235_);
v___x_3254_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_body_3235_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3336_; 
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3257_ = v___x_3254_;
v_isShared_3258_ = v_isSharedCheck_3336_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3254_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3336_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; uint8_t v___y_3266_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; uint8_t v_nondep_x27_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; uint8_t v_nondep_x27_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___x_3306_; 
v___x_3306_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v___y_3250_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; uint8_t v___x_3308_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3307_);
lean_dec_ref_known(v___x_3306_, 1);
v___x_3308_ = 1;
if (v_nondep_3239_ == 0)
{
if (v___y_3243_ == 0)
{
lean_dec(v_a_3307_);
v_nondep_x27_3289_ = v_nondep_3239_;
v___y_3290_ = v___y_3247_;
v___y_3291_ = v___y_3248_;
v___y_3292_ = v___y_3249_;
v___y_3293_ = v___y_3250_;
v___y_3294_ = v___y_3251_;
v___y_3295_ = v___y_3252_;
goto v___jp_3288_;
}
else
{
lean_object* v___x_3309_; uint8_t v___x_3310_; 
v___x_3309_ = l_Lean_Expr_fvarId_x21(v_x_3244_);
v___x_3310_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(v___x_3309_, v_a_3307_);
lean_dec(v_a_3307_);
lean_dec(v___x_3309_);
if (v___x_3310_ == 0)
{
lean_object* v___x_3311_; lean_object* v_visited_3312_; lean_object* v_types_3313_; lean_object* v_subst_3314_; lean_object* v_visitedClosed_3315_; lean_object* v_hasDepLetCache_3316_; lean_object* v_numConverted_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3327_; 
v___x_3311_ = lean_st_ref_take(v___y_3246_);
v_visited_3312_ = lean_ctor_get(v___x_3311_, 0);
v_types_3313_ = lean_ctor_get(v___x_3311_, 1);
v_subst_3314_ = lean_ctor_get(v___x_3311_, 2);
v_visitedClosed_3315_ = lean_ctor_get(v___x_3311_, 3);
v_hasDepLetCache_3316_ = lean_ctor_get(v___x_3311_, 4);
v_numConverted_3317_ = lean_ctor_get(v___x_3311_, 5);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3319_ = v___x_3311_;
v_isShared_3320_ = v_isSharedCheck_3327_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_numConverted_3317_);
lean_inc(v_hasDepLetCache_3316_);
lean_inc(v_visitedClosed_3315_);
lean_inc(v_subst_3314_);
lean_inc(v_types_3313_);
lean_inc(v_visited_3312_);
lean_dec(v___x_3311_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3327_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3324_; 
v___x_3321_ = lean_unsigned_to_nat(1u);
v___x_3322_ = lean_nat_add(v_numConverted_3317_, v___x_3321_);
lean_dec(v_numConverted_3317_);
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 5, v___x_3322_);
v___x_3324_ = v___x_3319_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_visited_3312_);
lean_ctor_set(v_reuseFailAlloc_3326_, 1, v_types_3313_);
lean_ctor_set(v_reuseFailAlloc_3326_, 2, v_subst_3314_);
lean_ctor_set(v_reuseFailAlloc_3326_, 3, v_visitedClosed_3315_);
lean_ctor_set(v_reuseFailAlloc_3326_, 4, v_hasDepLetCache_3316_);
lean_ctor_set(v_reuseFailAlloc_3326_, 5, v___x_3322_);
v___x_3324_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
lean_object* v___x_3325_; 
v___x_3325_ = lean_st_ref_put(v___y_3246_, v___x_3324_);
v_nondep_x27_3298_ = v___x_3308_;
v___y_3299_ = v___y_3247_;
v___y_3300_ = v___y_3248_;
v___y_3301_ = v___y_3249_;
v___y_3302_ = v___y_3250_;
v___y_3303_ = v___y_3251_;
v___y_3304_ = v___y_3252_;
goto v___jp_3297_;
}
}
}
else
{
v_nondep_x27_3289_ = v_nondep_3239_;
v___y_3290_ = v___y_3247_;
v___y_3291_ = v___y_3248_;
v___y_3292_ = v___y_3249_;
v___y_3293_ = v___y_3250_;
v___y_3294_ = v___y_3251_;
v___y_3295_ = v___y_3252_;
goto v___jp_3288_;
}
}
}
else
{
lean_dec(v_a_3307_);
v_nondep_x27_3298_ = v___x_3308_;
v___y_3299_ = v___y_3247_;
v___y_3300_ = v___y_3248_;
v___y_3301_ = v___y_3249_;
v___y_3302_ = v___y_3250_;
v___y_3303_ = v___y_3251_;
v___y_3304_ = v___y_3252_;
goto v___jp_3297_;
}
}
else
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3335_; 
lean_del_object(v___x_3257_);
lean_dec(v_a_3255_);
lean_dec_ref(v_e_3240_);
lean_dec_ref(v_a_3238_);
lean_dec_ref(v_a_3237_);
lean_dec(v_declName_3236_);
lean_dec_ref(v_body_3235_);
v_a_3328_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3330_ = v___x_3306_;
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3306_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3333_; 
if (v_isShared_3331_ == 0)
{
v___x_3333_ = v___x_3330_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3328_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
v___jp_3259_:
{
if (v___y_3266_ == 0)
{
lean_object* v___x_3267_; 
lean_del_object(v___x_3257_);
lean_dec_ref(v_e_3240_);
lean_dec_ref(v_body_3235_);
v___x_3267_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3236_, v_a_3237_, v_a_3238_, v_a_3255_, v_nondep_3239_, v___y_3260_, v___y_3262_, v___y_3264_, v___y_3261_, v___y_3265_, v___y_3263_);
return v___x_3267_;
}
else
{
size_t v___x_3268_; size_t v___x_3269_; uint8_t v___x_3270_; 
v___x_3268_ = lean_ptr_addr(v_body_3235_);
lean_dec_ref(v_body_3235_);
v___x_3269_ = lean_ptr_addr(v_a_3255_);
v___x_3270_ = lean_usize_dec_eq(v___x_3268_, v___x_3269_);
if (v___x_3270_ == 0)
{
lean_object* v___x_3271_; 
lean_del_object(v___x_3257_);
lean_dec_ref(v_e_3240_);
v___x_3271_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3236_, v_a_3237_, v_a_3238_, v_a_3255_, v_nondep_3239_, v___y_3260_, v___y_3262_, v___y_3264_, v___y_3261_, v___y_3265_, v___y_3263_);
return v___x_3271_;
}
else
{
lean_object* v___x_3273_; 
lean_dec(v_a_3255_);
lean_dec_ref(v_a_3238_);
lean_dec_ref(v_a_3237_);
lean_dec(v_declName_3236_);
if (v_isShared_3258_ == 0)
{
lean_ctor_set(v___x_3257_, 0, v_e_3240_);
v___x_3273_ = v___x_3257_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_e_3240_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
v___jp_3275_:
{
size_t v___x_3282_; size_t v___x_3283_; uint8_t v___x_3284_; 
v___x_3282_ = lean_ptr_addr(v_type_3241_);
v___x_3283_ = lean_ptr_addr(v_a_3237_);
v___x_3284_ = lean_usize_dec_eq(v___x_3282_, v___x_3283_);
if (v___x_3284_ == 0)
{
v___y_3260_ = v___y_3276_;
v___y_3261_ = v___y_3278_;
v___y_3262_ = v___y_3277_;
v___y_3263_ = v___y_3279_;
v___y_3264_ = v___y_3280_;
v___y_3265_ = v___y_3281_;
v___y_3266_ = v___x_3284_;
goto v___jp_3259_;
}
else
{
size_t v___x_3285_; size_t v___x_3286_; uint8_t v___x_3287_; 
v___x_3285_ = lean_ptr_addr(v_value_3242_);
v___x_3286_ = lean_ptr_addr(v_a_3238_);
v___x_3287_ = lean_usize_dec_eq(v___x_3285_, v___x_3286_);
v___y_3260_ = v___y_3276_;
v___y_3261_ = v___y_3278_;
v___y_3262_ = v___y_3277_;
v___y_3263_ = v___y_3279_;
v___y_3264_ = v___y_3280_;
v___y_3265_ = v___y_3281_;
v___y_3266_ = v___x_3287_;
goto v___jp_3259_;
}
}
v___jp_3288_:
{
if (v_nondep_3239_ == 0)
{
v___y_3276_ = v___y_3290_;
v___y_3277_ = v___y_3291_;
v___y_3278_ = v___y_3293_;
v___y_3279_ = v___y_3295_;
v___y_3280_ = v___y_3292_;
v___y_3281_ = v___y_3294_;
goto v___jp_3275_;
}
else
{
lean_object* v___x_3296_; 
lean_del_object(v___x_3257_);
lean_dec_ref(v_e_3240_);
lean_dec_ref(v_body_3235_);
v___x_3296_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3236_, v_a_3237_, v_a_3238_, v_a_3255_, v_nondep_x27_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
return v___x_3296_;
}
}
v___jp_3297_:
{
if (v_nondep_3239_ == 0)
{
lean_object* v___x_3305_; 
lean_del_object(v___x_3257_);
lean_dec_ref(v_e_3240_);
lean_dec_ref(v_body_3235_);
v___x_3305_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3236_, v_a_3237_, v_a_3238_, v_a_3255_, v_nondep_x27_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
return v___x_3305_;
}
else
{
v___y_3276_ = v___y_3299_;
v___y_3277_ = v___y_3300_;
v___y_3278_ = v___y_3302_;
v___y_3279_ = v___y_3304_;
v___y_3280_ = v___y_3301_;
v___y_3281_ = v___y_3303_;
goto v___jp_3275_;
}
}
}
}
else
{
lean_dec_ref(v_e_3240_);
lean_dec_ref(v_a_3238_);
lean_dec_ref(v_a_3237_);
lean_dec(v_declName_3236_);
lean_dec_ref(v_body_3235_);
return v___x_3254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1___boxed(lean_object** _args){
lean_object* v_body_3337_ = _args[0];
lean_object* v_declName_3338_ = _args[1];
lean_object* v_a_3339_ = _args[2];
lean_object* v_a_3340_ = _args[3];
lean_object* v_nondep_3341_ = _args[4];
lean_object* v_e_3342_ = _args[5];
lean_object* v_type_3343_ = _args[6];
lean_object* v_value_3344_ = _args[7];
lean_object* v___y_3345_ = _args[8];
lean_object* v_x_3346_ = _args[9];
lean_object* v___y_3347_ = _args[10];
lean_object* v___y_3348_ = _args[11];
lean_object* v___y_3349_ = _args[12];
lean_object* v___y_3350_ = _args[13];
lean_object* v___y_3351_ = _args[14];
lean_object* v___y_3352_ = _args[15];
lean_object* v___y_3353_ = _args[16];
lean_object* v___y_3354_ = _args[17];
lean_object* v___y_3355_ = _args[18];
_start:
{
uint8_t v_nondep_82522__boxed_3356_; uint8_t v___y_82525__boxed_3357_; lean_object* v_res_3358_; 
v_nondep_82522__boxed_3356_ = lean_unbox(v_nondep_3341_);
v___y_82525__boxed_3357_ = lean_unbox(v___y_3345_);
v_res_3358_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1(v_body_3337_, v_declName_3338_, v_a_3339_, v_a_3340_, v_nondep_82522__boxed_3356_, v_e_3342_, v_type_3343_, v_value_3344_, v___y_82525__boxed_3357_, v_x_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec_ref(v_x_3346_);
lean_dec_ref(v_value_3344_);
lean_dec_ref(v_type_3343_);
return v_res_3358_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1(void){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3360_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_3361_ = lean_unsigned_to_nat(9u);
v___x_3362_ = lean_unsigned_to_nat(263u);
v___x_3363_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__0));
v___x_3364_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0));
v___x_3365_ = l_mkPanicMessageWithDecl(v___x_3364_, v___x_3363_, v___x_3362_, v___x_3361_, v___x_3360_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(lean_object* v_e_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_){
_start:
{
lean_object* v___y_3377_; lean_object* v___y_3378_; uint8_t v___y_3379_; 
switch(lean_obj_tag(v_e_3366_))
{
case 5:
{
lean_object* v_fn_3389_; lean_object* v_arg_3390_; lean_object* v___y_3392_; lean_object* v_a_3393_; lean_object* v___x_3414_; 
v_fn_3389_ = lean_ctor_get(v_e_3366_, 0);
lean_inc_ref_n(v_fn_3389_, 2);
v_arg_3390_ = lean_ctor_get(v_e_3366_, 1);
lean_inc_ref(v_arg_3390_);
v___x_3414_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_fn_3389_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; lean_object* v___x_3416_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
lean_inc(v_a_3415_);
lean_dec_ref_known(v___x_3414_, 1);
lean_inc_ref(v_arg_3390_);
v___x_3416_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_arg_3390_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3434_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3419_ = v___x_3416_;
v_isShared_3420_ = v_isSharedCheck_3434_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3416_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3434_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
uint8_t v___y_3422_; size_t v___x_3428_; size_t v___x_3429_; uint8_t v___x_3430_; 
v___x_3428_ = lean_ptr_addr(v_fn_3389_);
v___x_3429_ = lean_ptr_addr(v_a_3415_);
v___x_3430_ = lean_usize_dec_eq(v___x_3428_, v___x_3429_);
if (v___x_3430_ == 0)
{
v___y_3422_ = v___x_3430_;
goto v___jp_3421_;
}
else
{
size_t v___x_3431_; size_t v___x_3432_; uint8_t v___x_3433_; 
v___x_3431_ = lean_ptr_addr(v_arg_3390_);
v___x_3432_ = lean_ptr_addr(v_a_3417_);
v___x_3433_ = lean_usize_dec_eq(v___x_3431_, v___x_3432_);
v___y_3422_ = v___x_3433_;
goto v___jp_3421_;
}
v___jp_3421_:
{
if (v___y_3422_ == 0)
{
lean_object* v___x_3423_; 
lean_del_object(v___x_3419_);
lean_dec_ref_known(v_e_3366_, 2);
v___x_3423_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(v_a_3415_, v_a_3417_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
v___y_3392_ = v___x_3423_;
v_a_3393_ = v_a_3424_;
goto v___jp_3391_;
}
else
{
lean_dec_ref(v_arg_3390_);
lean_dec_ref(v_fn_3389_);
return v___x_3423_;
}
}
else
{
lean_object* v___x_3426_; 
lean_dec(v_a_3417_);
lean_dec(v_a_3415_);
lean_inc_ref(v_e_3366_);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v_e_3366_);
v___x_3426_ = v___x_3419_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_e_3366_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
v___y_3392_ = v___x_3426_;
v_a_3393_ = v_e_3366_;
goto v___jp_3391_;
}
}
}
}
}
else
{
lean_dec(v_a_3415_);
lean_dec_ref(v_arg_3390_);
lean_dec_ref_known(v_e_3366_, 2);
lean_dec_ref(v_fn_3389_);
return v___x_3416_;
}
}
else
{
lean_dec_ref(v_arg_3390_);
lean_dec_ref_known(v_e_3366_, 2);
lean_dec_ref(v_fn_3389_);
return v___x_3414_;
}
v___jp_3391_:
{
lean_object* v_numCandidates_3394_; lean_object* v___x_3395_; uint8_t v___x_3396_; 
v_numCandidates_3394_ = lean_ctor_get(v_a_3367_, 1);
v___x_3395_ = lean_unsigned_to_nat(0u);
v___x_3396_ = lean_nat_dec_lt(v___x_3395_, v_numCandidates_3394_);
if (v___x_3396_ == 0)
{
lean_dec_ref(v_a_3393_);
lean_dec_ref(v_arg_3390_);
lean_dec_ref(v_fn_3389_);
return v___y_3392_;
}
else
{
lean_object* v___x_3397_; 
lean_dec_ref(v___y_3392_);
v___x_3397_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp(v_fn_3389_, v_arg_3390_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3404_; 
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3404_ == 0)
{
lean_object* v_unused_3405_; 
v_unused_3405_ = lean_ctor_get(v___x_3397_, 0);
lean_dec(v_unused_3405_);
v___x_3399_ = v___x_3397_;
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
else
{
lean_dec(v___x_3397_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v___x_3402_; 
if (v_isShared_3400_ == 0)
{
lean_ctor_set(v___x_3399_, 0, v_a_3393_);
v___x_3402_ = v___x_3399_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_a_3393_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_dec_ref(v_a_3393_);
v_a_3406_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3397_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3397_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
}
}
case 10:
{
lean_object* v_data_3435_; lean_object* v_expr_3436_; lean_object* v___x_3437_; 
v_data_3435_ = lean_ctor_get(v_e_3366_, 0);
v_expr_3436_ = lean_ctor_get(v_e_3366_, 1);
lean_inc_ref(v_expr_3436_);
v___x_3437_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_expr_3436_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3449_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3440_ = v___x_3437_;
v_isShared_3441_ = v_isSharedCheck_3449_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3437_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3449_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
size_t v___x_3442_; size_t v___x_3443_; uint8_t v___x_3444_; 
v___x_3442_ = lean_ptr_addr(v_expr_3436_);
v___x_3443_ = lean_ptr_addr(v_a_3438_);
v___x_3444_ = lean_usize_dec_eq(v___x_3442_, v___x_3443_);
if (v___x_3444_ == 0)
{
lean_object* v___x_3445_; 
lean_inc(v_data_3435_);
lean_del_object(v___x_3440_);
lean_dec_ref_known(v_e_3366_, 2);
v___x_3445_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(v_data_3435_, v_a_3438_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
return v___x_3445_;
}
else
{
lean_object* v___x_3447_; 
lean_dec(v_a_3438_);
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 0, v_e_3366_);
v___x_3447_ = v___x_3440_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_e_3366_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3366_, 2);
return v___x_3437_;
}
}
case 11:
{
lean_object* v_typeName_3450_; lean_object* v_idx_3451_; lean_object* v_struct_3452_; lean_object* v___y_3454_; lean_object* v_a_3455_; lean_object* v___x_3462_; 
v_typeName_3450_ = lean_ctor_get(v_e_3366_, 0);
v_idx_3451_ = lean_ctor_get(v_e_3366_, 1);
v_struct_3452_ = lean_ctor_get(v_e_3366_, 2);
lean_inc_ref(v_struct_3452_);
v___x_3462_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_struct_3452_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3475_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3465_ = v___x_3462_;
v_isShared_3466_ = v_isSharedCheck_3475_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3462_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3475_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
size_t v___x_3467_; size_t v___x_3468_; uint8_t v___x_3469_; 
v___x_3467_ = lean_ptr_addr(v_struct_3452_);
v___x_3468_ = lean_ptr_addr(v_a_3463_);
v___x_3469_ = lean_usize_dec_eq(v___x_3467_, v___x_3468_);
if (v___x_3469_ == 0)
{
lean_object* v___x_3470_; 
lean_del_object(v___x_3465_);
lean_inc(v_idx_3451_);
lean_inc(v_typeName_3450_);
v___x_3470_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(v_typeName_3450_, v_idx_3451_, v_a_3463_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3471_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3471_);
v___y_3454_ = v___x_3470_;
v_a_3455_ = v_a_3471_;
goto v___jp_3453_;
}
else
{
lean_dec_ref_known(v_e_3366_, 3);
return v___x_3470_;
}
}
else
{
lean_object* v___x_3473_; 
lean_dec(v_a_3463_);
lean_inc_ref(v_e_3366_);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 0, v_e_3366_);
v___x_3473_ = v___x_3465_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_e_3366_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_inc_ref(v_e_3366_);
v___y_3454_ = v___x_3473_;
v_a_3455_ = v_e_3366_;
goto v___jp_3453_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3366_, 3);
return v___x_3462_;
}
v___jp_3453_:
{
lean_object* v_numCandidates_3456_; lean_object* v_cleanSuffix_3457_; lean_object* v___x_3458_; uint8_t v___x_3459_; 
v_numCandidates_3456_ = lean_ctor_get(v_a_3367_, 1);
v_cleanSuffix_3457_ = lean_ctor_get(v_a_3367_, 2);
v___x_3458_ = lean_unsigned_to_nat(0u);
v___x_3459_ = lean_nat_dec_lt(v___x_3458_, v_numCandidates_3456_);
if (v___x_3459_ == 0)
{
v___y_3377_ = v___y_3454_;
v___y_3378_ = v_a_3455_;
v___y_3379_ = v___x_3459_;
goto v___jp_3376_;
}
else
{
lean_object* v___x_3460_; uint8_t v___x_3461_; 
v___x_3460_ = l_Lean_Expr_looseBVarRange(v_struct_3452_);
v___x_3461_ = lean_nat_dec_le(v___x_3460_, v_cleanSuffix_3457_);
lean_dec(v___x_3460_);
if (v___x_3461_ == 0)
{
v___y_3377_ = v___y_3454_;
v___y_3378_ = v_a_3455_;
v___y_3379_ = v___x_3459_;
goto v___jp_3376_;
}
else
{
lean_dec_ref(v_a_3455_);
lean_dec_ref_known(v_e_3366_, 3);
return v___y_3454_;
}
}
}
}
case 6:
{
lean_object* v_binderName_3476_; lean_object* v_binderType_3477_; lean_object* v_body_3478_; uint8_t v_binderInfo_3479_; lean_object* v___x_3480_; 
v_binderName_3476_ = lean_ctor_get(v_e_3366_, 0);
lean_inc(v_binderName_3476_);
v_binderType_3477_ = lean_ctor_get(v_e_3366_, 1);
lean_inc_ref_n(v_binderType_3477_, 2);
v_body_3478_ = lean_ctor_get(v_e_3366_, 2);
lean_inc_ref(v_body_3478_);
v_binderInfo_3479_ = lean_ctor_get_uint8(v_e_3366_, sizeof(void*)*3 + 8);
v___x_3480_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_binderType_3477_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3482_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
lean_inc_n(v_a_3481_, 2);
lean_dec_ref_known(v___x_3480_, 1);
v___x_3482_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3481_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v_a_3483_; lean_object* v___x_3484_; 
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
lean_inc_n(v_a_3483_, 2);
lean_dec_ref_known(v___x_3482_, 1);
v___x_3484_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_binderType_3477_, v_a_3483_, v_a_3367_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v_cleanSuffix_3485_; lean_object* v___x_3486_; lean_object* v___f_3487_; lean_object* v___x_3488_; uint8_t v___y_3490_; lean_object* v___x_3493_; uint8_t v___x_3494_; 
lean_dec_ref_known(v___x_3484_, 1);
v_cleanSuffix_3485_ = lean_ctor_get(v_a_3367_, 2);
v___x_3486_ = lean_box(v_binderInfo_3479_);
lean_inc_ref(v_binderType_3477_);
lean_inc(v_binderName_3476_);
v___f_3487_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0___boxed), 16, 6);
lean_closure_set(v___f_3487_, 0, v_body_3478_);
lean_closure_set(v___f_3487_, 1, v_binderName_3476_);
lean_closure_set(v___f_3487_, 2, v___x_3486_);
lean_closure_set(v___f_3487_, 3, v_a_3481_);
lean_closure_set(v___f_3487_, 4, v_e_3366_);
lean_closure_set(v___f_3487_, 5, v_binderType_3477_);
v___x_3488_ = lean_box(0);
v___x_3493_ = l_Lean_Expr_looseBVarRange(v_binderType_3477_);
lean_dec_ref(v_binderType_3477_);
v___x_3494_ = lean_nat_dec_le(v___x_3493_, v_cleanSuffix_3485_);
lean_dec(v___x_3493_);
if (v___x_3494_ == 0)
{
uint8_t v___x_3495_; 
v___x_3495_ = 1;
v___y_3490_ = v___x_3495_;
goto v___jp_3489_;
}
else
{
uint8_t v___x_3496_; 
v___x_3496_ = 0;
v___y_3490_ = v___x_3496_;
goto v___jp_3489_;
}
v___jp_3489_:
{
uint8_t v___x_3491_; lean_object* v___x_3492_; 
v___x_3491_ = 0;
v___x_3492_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_binderName_3476_, v_a_3483_, v___x_3488_, v___y_3490_, v___x_3491_, v___f_3487_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
return v___x_3492_;
}
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_dec(v_a_3483_);
lean_dec(v_a_3481_);
lean_dec_ref(v_body_3478_);
lean_dec_ref(v_binderType_3477_);
lean_dec_ref_known(v_e_3366_, 3);
lean_dec(v_binderName_3476_);
v_a_3497_ = lean_ctor_get(v___x_3484_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3484_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3484_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
else
{
lean_dec(v_a_3481_);
lean_dec_ref(v_body_3478_);
lean_dec_ref(v_binderType_3477_);
lean_dec_ref_known(v_e_3366_, 3);
lean_dec(v_binderName_3476_);
return v___x_3482_;
}
}
else
{
lean_dec_ref(v_body_3478_);
lean_dec_ref(v_binderType_3477_);
lean_dec_ref_known(v_e_3366_, 3);
lean_dec(v_binderName_3476_);
return v___x_3480_;
}
}
case 7:
{
lean_object* v___x_3505_; 
v___x_3505_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(v_e_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
return v___x_3505_;
}
case 8:
{
lean_object* v_declName_3506_; lean_object* v_type_3507_; lean_object* v_value_3508_; lean_object* v_body_3509_; uint8_t v_nondep_3510_; lean_object* v___x_3511_; 
v_declName_3506_ = lean_ctor_get(v_e_3366_, 0);
lean_inc(v_declName_3506_);
v_type_3507_ = lean_ctor_get(v_e_3366_, 1);
lean_inc_ref_n(v_type_3507_, 2);
v_value_3508_ = lean_ctor_get(v_e_3366_, 2);
lean_inc_ref(v_value_3508_);
v_body_3509_ = lean_ctor_get(v_e_3366_, 3);
lean_inc_ref(v_body_3509_);
v_nondep_3510_ = lean_ctor_get_uint8(v_e_3366_, sizeof(void*)*4 + 8);
v___x_3511_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_type_3507_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3513_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3512_);
lean_dec_ref_known(v___x_3511_, 1);
lean_inc_ref(v_value_3508_);
v___x_3513_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_value_3508_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___x_3513_, 1);
lean_inc(v_a_3512_);
v___x_3515_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3512_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3600_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3518_ = v___x_3515_;
v_isShared_3519_ = v_isSharedCheck_3600_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3515_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3600_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v_numCandidates_3520_; lean_object* v_cleanSuffix_3521_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; uint8_t v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; uint8_t v___y_3533_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___x_3563_; uint8_t v___x_3564_; 
v_numCandidates_3520_ = lean_ctor_get(v_a_3367_, 1);
v_cleanSuffix_3521_ = lean_ctor_get(v_a_3367_, 2);
v___x_3563_ = lean_unsigned_to_nat(0u);
v___x_3564_ = lean_nat_dec_lt(v___x_3563_, v_numCandidates_3520_);
if (v___x_3564_ == 0)
{
v___y_3549_ = v_a_3367_;
v___y_3550_ = v_a_3368_;
v___y_3551_ = v_a_3369_;
v___y_3552_ = v_a_3370_;
v___y_3553_ = v_a_3371_;
v___y_3554_ = v_a_3372_;
v___y_3555_ = v_a_3373_;
v___y_3556_ = v_a_3374_;
goto v___jp_3548_;
}
else
{
lean_object* v___x_3565_; 
lean_inc(v_a_3516_);
v___x_3565_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_type_3507_, v_a_3516_, v_a_3367_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v___x_3588_; uint8_t v___x_3589_; 
lean_dec_ref_known(v___x_3565_, 1);
v___x_3588_ = l_Lean_Expr_looseBVarRange(v_type_3507_);
v___x_3589_ = lean_nat_dec_le(v___x_3588_, v_cleanSuffix_3521_);
lean_dec(v___x_3588_);
if (v___x_3589_ == 0)
{
goto v___jp_3566_;
}
else
{
lean_object* v___x_3590_; uint8_t v___x_3591_; 
v___x_3590_ = l_Lean_Expr_looseBVarRange(v_value_3508_);
v___x_3591_ = lean_nat_dec_le(v___x_3590_, v_cleanSuffix_3521_);
lean_dec(v___x_3590_);
if (v___x_3591_ == 0)
{
goto v___jp_3566_;
}
else
{
v___y_3549_ = v_a_3367_;
v___y_3550_ = v_a_3368_;
v___y_3551_ = v_a_3369_;
v___y_3552_ = v_a_3370_;
v___y_3553_ = v_a_3371_;
v___y_3554_ = v_a_3372_;
v___y_3555_ = v_a_3373_;
v___y_3556_ = v_a_3374_;
goto v___jp_3548_;
}
}
v___jp_3566_:
{
uint8_t v___x_3567_; 
v___x_3567_ = l_Lean_Expr_isLambda(v_value_3508_);
if (v___x_3567_ == 0)
{
lean_object* v___x_3568_; 
lean_inc_ref(v_value_3508_);
v___x_3568_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_value_3508_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3570_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc(v_a_3569_);
lean_dec_ref_known(v___x_3568_, 1);
lean_inc(v_a_3516_);
v___x_3570_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_a_3569_, v_a_3516_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_dec_ref_known(v___x_3570_, 1);
v___y_3549_ = v_a_3367_;
v___y_3550_ = v_a_3368_;
v___y_3551_ = v_a_3369_;
v___y_3552_ = v_a_3370_;
v___y_3553_ = v_a_3371_;
v___y_3554_ = v_a_3372_;
v___y_3555_ = v_a_3373_;
v___y_3556_ = v_a_3374_;
goto v___jp_3548_;
}
else
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3578_; 
lean_del_object(v___x_3518_);
lean_dec(v_a_3516_);
lean_dec(v_a_3514_);
lean_dec(v_a_3512_);
lean_dec_ref(v_body_3509_);
lean_dec_ref(v_value_3508_);
lean_dec_ref(v_type_3507_);
lean_dec(v_declName_3506_);
lean_dec_ref_known(v_e_3366_, 4);
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3573_ = v___x_3570_;
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3570_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3574_ == 0)
{
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3571_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
else
{
lean_del_object(v___x_3518_);
lean_dec(v_a_3516_);
lean_dec(v_a_3514_);
lean_dec(v_a_3512_);
lean_dec_ref(v_body_3509_);
lean_dec_ref(v_value_3508_);
lean_dec_ref(v_type_3507_);
lean_dec(v_declName_3506_);
lean_dec_ref_known(v_e_3366_, 4);
return v___x_3568_;
}
}
else
{
lean_object* v___x_3579_; 
lean_inc(v_a_3516_);
lean_inc_ref(v_value_3508_);
v___x_3579_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_value_3508_, v_a_3516_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_dec_ref_known(v___x_3579_, 1);
v___y_3549_ = v_a_3367_;
v___y_3550_ = v_a_3368_;
v___y_3551_ = v_a_3369_;
v___y_3552_ = v_a_3370_;
v___y_3553_ = v_a_3371_;
v___y_3554_ = v_a_3372_;
v___y_3555_ = v_a_3373_;
v___y_3556_ = v_a_3374_;
goto v___jp_3548_;
}
else
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
lean_del_object(v___x_3518_);
lean_dec(v_a_3516_);
lean_dec(v_a_3514_);
lean_dec(v_a_3512_);
lean_dec_ref(v_body_3509_);
lean_dec_ref(v_value_3508_);
lean_dec_ref(v_type_3507_);
lean_dec(v_declName_3506_);
lean_dec_ref_known(v_e_3366_, 4);
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3579_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3579_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
}
}
else
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
lean_del_object(v___x_3518_);
lean_dec(v_a_3516_);
lean_dec(v_a_3514_);
lean_dec(v_a_3512_);
lean_dec_ref(v_body_3509_);
lean_dec_ref(v_value_3508_);
lean_dec_ref(v_type_3507_);
lean_dec(v_declName_3506_);
lean_dec_ref_known(v_e_3366_, 4);
v_a_3592_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3565_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3565_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
}
v___jp_3522_:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___f_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3540_; 
v___x_3534_ = lean_box(v_nondep_3510_);
v___x_3535_ = lean_box(v___y_3533_);
lean_inc_ref(v_type_3507_);
lean_inc(v_declName_3506_);
v___f_3536_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1___boxed), 19, 9);
lean_closure_set(v___f_3536_, 0, v_body_3509_);
lean_closure_set(v___f_3536_, 1, v_declName_3506_);
lean_closure_set(v___f_3536_, 2, v_a_3512_);
lean_closure_set(v___f_3536_, 3, v_a_3514_);
lean_closure_set(v___f_3536_, 4, v___x_3534_);
lean_closure_set(v___f_3536_, 5, v_e_3366_);
lean_closure_set(v___f_3536_, 6, v_type_3507_);
lean_closure_set(v___f_3536_, 7, v_value_3508_);
lean_closure_set(v___f_3536_, 8, v___x_3535_);
v___x_3537_ = lean_box(v_nondep_3510_);
v___x_3538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3538_, 0, v___y_3526_);
lean_ctor_set(v___x_3538_, 1, v___x_3537_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set_tag(v___x_3518_, 1);
lean_ctor_set(v___x_3518_, 0, v___x_3538_);
v___x_3540_ = v___x_3518_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___x_3538_);
v___x_3540_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
if (v___y_3529_ == 0)
{
lean_object* v___x_3541_; uint8_t v___x_3542_; 
v___x_3541_ = l_Lean_Expr_looseBVarRange(v_type_3507_);
lean_dec_ref(v_type_3507_);
v___x_3542_ = lean_nat_dec_le(v___x_3541_, v_cleanSuffix_3521_);
lean_dec(v___x_3541_);
if (v___x_3542_ == 0)
{
uint8_t v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = 1;
v___x_3544_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_declName_3506_, v_a_3516_, v___x_3540_, v___x_3543_, v___y_3533_, v___f_3536_, v___y_3525_, v___y_3528_, v___y_3532_, v___y_3524_, v___y_3531_, v___y_3523_, v___y_3530_, v___y_3527_);
return v___x_3544_;
}
else
{
lean_object* v___x_3545_; 
v___x_3545_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_declName_3506_, v_a_3516_, v___x_3540_, v___y_3529_, v___y_3533_, v___f_3536_, v___y_3525_, v___y_3528_, v___y_3532_, v___y_3524_, v___y_3531_, v___y_3523_, v___y_3530_, v___y_3527_);
return v___x_3545_;
}
}
else
{
lean_object* v___x_3546_; 
lean_dec_ref(v_type_3507_);
v___x_3546_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_declName_3506_, v_a_3516_, v___x_3540_, v___y_3529_, v___y_3533_, v___f_3536_, v___y_3525_, v___y_3528_, v___y_3532_, v___y_3524_, v___y_3531_, v___y_3523_, v___y_3530_, v___y_3527_);
return v___x_3546_;
}
}
}
v___jp_3548_:
{
lean_object* v___x_3557_; 
lean_inc(v_a_3514_);
v___x_3557_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3514_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
if (lean_obj_tag(v___x_3557_) == 0)
{
if (v_nondep_3510_ == 0)
{
lean_object* v_a_3558_; uint8_t v___x_3559_; uint8_t v___x_3560_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref_known(v___x_3557_, 1);
v___x_3559_ = 1;
v___x_3560_ = l_Lean_Expr_hasExprMVar(v_e_3366_);
if (v___x_3560_ == 0)
{
v___y_3523_ = v___y_3554_;
v___y_3524_ = v___y_3552_;
v___y_3525_ = v___y_3549_;
v___y_3526_ = v_a_3558_;
v___y_3527_ = v___y_3556_;
v___y_3528_ = v___y_3550_;
v___y_3529_ = v___x_3559_;
v___y_3530_ = v___y_3555_;
v___y_3531_ = v___y_3553_;
v___y_3532_ = v___y_3551_;
v___y_3533_ = v___x_3559_;
goto v___jp_3522_;
}
else
{
v___y_3523_ = v___y_3554_;
v___y_3524_ = v___y_3552_;
v___y_3525_ = v___y_3549_;
v___y_3526_ = v_a_3558_;
v___y_3527_ = v___y_3556_;
v___y_3528_ = v___y_3550_;
v___y_3529_ = v___x_3559_;
v___y_3530_ = v___y_3555_;
v___y_3531_ = v___y_3553_;
v___y_3532_ = v___y_3551_;
v___y_3533_ = v_nondep_3510_;
goto v___jp_3522_;
}
}
else
{
lean_object* v_a_3561_; uint8_t v___x_3562_; 
v_a_3561_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3561_);
lean_dec_ref_known(v___x_3557_, 1);
v___x_3562_ = 0;
v___y_3523_ = v___y_3554_;
v___y_3524_ = v___y_3552_;
v___y_3525_ = v___y_3549_;
v___y_3526_ = v_a_3561_;
v___y_3527_ = v___y_3556_;
v___y_3528_ = v___y_3550_;
v___y_3529_ = v___x_3562_;
v___y_3530_ = v___y_3555_;
v___y_3531_ = v___y_3553_;
v___y_3532_ = v___y_3551_;
v___y_3533_ = v___x_3562_;
goto v___jp_3522_;
}
}
else
{
lean_del_object(v___x_3518_);
lean_dec(v_a_3516_);
lean_dec(v_a_3514_);
lean_dec(v_a_3512_);
lean_dec_ref(v_body_3509_);
lean_dec_ref(v_value_3508_);
lean_dec_ref(v_type_3507_);
lean_dec(v_declName_3506_);
lean_dec_ref_known(v_e_3366_, 4);
return v___x_3557_;
}
}
}
}
else
{
lean_dec(v_a_3514_);
lean_dec(v_a_3512_);
lean_dec_ref(v_body_3509_);
lean_dec_ref(v_value_3508_);
lean_dec_ref(v_type_3507_);
lean_dec(v_declName_3506_);
lean_dec_ref_known(v_e_3366_, 4);
return v___x_3515_;
}
}
else
{
lean_dec(v_a_3512_);
lean_dec_ref(v_body_3509_);
lean_dec_ref(v_value_3508_);
lean_dec_ref(v_type_3507_);
lean_dec(v_declName_3506_);
lean_dec_ref_known(v_e_3366_, 4);
return v___x_3513_;
}
}
else
{
lean_dec_ref(v_body_3509_);
lean_dec_ref(v_value_3508_);
lean_dec_ref(v_type_3507_);
lean_dec(v_declName_3506_);
lean_dec_ref_known(v_e_3366_, 4);
return v___x_3511_;
}
}
default: 
{
lean_object* v___x_3601_; lean_object* v___x_3602_; 
lean_dec_ref(v_e_3366_);
v___x_3601_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1);
v___x_3602_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(v___x_3601_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
return v___x_3602_;
}
}
v___jp_3376_:
{
if (v___y_3379_ == 0)
{
lean_dec_ref(v___y_3378_);
lean_dec_ref(v_e_3366_);
return v___y_3377_;
}
else
{
lean_object* v___x_3380_; 
lean_dec_ref(v___y_3377_);
v___x_3380_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(v_e_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3387_; 
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3387_ == 0)
{
lean_object* v_unused_3388_; 
v_unused_3388_ = lean_ctor_get(v___x_3380_, 0);
lean_dec(v_unused_3388_);
v___x_3382_ = v___x_3380_;
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
else
{
lean_dec(v___x_3380_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 0, v___y_3378_);
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___y_3378_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
else
{
lean_dec_ref(v___y_3378_);
return v___x_3380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(lean_object* v_e_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_){
_start:
{
lean_object* v___x_3612_; lean_object* v_visitedClosed_3613_; lean_object* v___x_3614_; 
v___x_3612_ = lean_st_ref_get(v_a_3604_);
v_visitedClosed_3613_ = lean_ctor_get(v___x_3612_, 3);
lean_inc_ref(v_visitedClosed_3613_);
lean_dec(v___x_3612_);
v___x_3614_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_visitedClosed_3613_, v_e_3603_);
lean_dec_ref(v_visitedClosed_3613_);
if (lean_obj_tag(v___x_3614_) == 1)
{
lean_object* v_val_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_dec_ref(v_e_3603_);
v_val_3615_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3614_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_val_3615_);
lean_dec(v___x_3614_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
lean_ctor_set_tag(v___x_3617_, 0);
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_val_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
else
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v_visited_3625_; lean_object* v_types_3626_; lean_object* v_subst_3627_; lean_object* v_visitedClosed_3628_; lean_object* v_hasDepLetCache_3629_; lean_object* v_numConverted_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3700_; 
lean_dec(v___x_3614_);
v___x_3623_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2);
v___x_3624_ = lean_st_ref_take(v_a_3604_);
v_visited_3625_ = lean_ctor_get(v___x_3624_, 0);
v_types_3626_ = lean_ctor_get(v___x_3624_, 1);
v_subst_3627_ = lean_ctor_get(v___x_3624_, 2);
v_visitedClosed_3628_ = lean_ctor_get(v___x_3624_, 3);
v_hasDepLetCache_3629_ = lean_ctor_get(v___x_3624_, 4);
v_numConverted_3630_ = lean_ctor_get(v___x_3624_, 5);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3632_ = v___x_3624_;
v_isShared_3633_ = v_isSharedCheck_3700_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_numConverted_3630_);
lean_inc(v_hasDepLetCache_3629_);
lean_inc(v_visitedClosed_3628_);
lean_inc(v_subst_3627_);
lean_inc(v_types_3626_);
lean_inc(v_visited_3625_);
lean_dec(v___x_3624_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3700_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3634_; lean_object* v___x_3636_; 
v___x_3634_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 2, v___x_3634_);
lean_ctor_set(v___x_3632_, 1, v___x_3634_);
lean_ctor_set(v___x_3632_, 0, v___x_3634_);
v___x_3636_ = v___x_3632_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3634_);
lean_ctor_set(v_reuseFailAlloc_3699_, 1, v___x_3634_);
lean_ctor_set(v_reuseFailAlloc_3699_, 2, v___x_3634_);
lean_ctor_set(v_reuseFailAlloc_3699_, 3, v_visitedClosed_3628_);
lean_ctor_set(v_reuseFailAlloc_3699_, 4, v_hasDepLetCache_3629_);
lean_ctor_set(v_reuseFailAlloc_3699_, 5, v_numConverted_3630_);
v___x_3636_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
lean_object* v___x_3637_; lean_object* v_r_3638_; 
v___x_3637_ = lean_st_ref_put(v_a_3604_, v___x_3636_);
lean_inc_ref(v_e_3603_);
v_r_3638_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(v_e_3603_, v___x_3623_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_);
if (lean_obj_tag(v_r_3638_) == 0)
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3679_; 
v_a_3639_ = lean_ctor_get(v_r_3638_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v_r_3638_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3641_ = v_r_3638_;
v_isShared_3642_ = v_isSharedCheck_3679_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v_r_3638_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3679_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3644_; 
lean_inc(v_a_3639_);
if (v_isShared_3642_ == 0)
{
lean_ctor_set_tag(v___x_3641_, 1);
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3639_);
v___x_3644_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
lean_object* v___x_3645_; 
v___x_3645_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(v_a_3604_, v_visited_3625_, v_types_3626_, v_subst_3627_, v___x_3644_);
lean_dec_ref(v___x_3644_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3668_; 
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3668_ == 0)
{
lean_object* v_unused_3669_; 
v_unused_3669_ = lean_ctor_get(v___x_3645_, 0);
lean_dec(v_unused_3669_);
v___x_3647_ = v___x_3645_;
v_isShared_3648_ = v_isSharedCheck_3668_;
goto v_resetjp_3646_;
}
else
{
lean_dec(v___x_3645_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3668_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3649_; lean_object* v_visited_3650_; lean_object* v_types_3651_; lean_object* v_subst_3652_; lean_object* v_visitedClosed_3653_; lean_object* v_hasDepLetCache_3654_; lean_object* v_numConverted_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3667_; 
v___x_3649_ = lean_st_ref_take(v_a_3604_);
v_visited_3650_ = lean_ctor_get(v___x_3649_, 0);
v_types_3651_ = lean_ctor_get(v___x_3649_, 1);
v_subst_3652_ = lean_ctor_get(v___x_3649_, 2);
v_visitedClosed_3653_ = lean_ctor_get(v___x_3649_, 3);
v_hasDepLetCache_3654_ = lean_ctor_get(v___x_3649_, 4);
v_numConverted_3655_ = lean_ctor_get(v___x_3649_, 5);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3657_ = v___x_3649_;
v_isShared_3658_ = v_isSharedCheck_3667_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_numConverted_3655_);
lean_inc(v_hasDepLetCache_3654_);
lean_inc(v_visitedClosed_3653_);
lean_inc(v_subst_3652_);
lean_inc(v_types_3651_);
lean_inc(v_visited_3650_);
lean_dec(v___x_3649_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3667_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3659_; lean_object* v___x_3661_; 
lean_inc(v_a_3639_);
v___x_3659_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_visitedClosed_3653_, v_e_3603_, v_a_3639_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 3, v___x_3659_);
v___x_3661_ = v___x_3657_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_visited_3650_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v_types_3651_);
lean_ctor_set(v_reuseFailAlloc_3666_, 2, v_subst_3652_);
lean_ctor_set(v_reuseFailAlloc_3666_, 3, v___x_3659_);
lean_ctor_set(v_reuseFailAlloc_3666_, 4, v_hasDepLetCache_3654_);
lean_ctor_set(v_reuseFailAlloc_3666_, 5, v_numConverted_3655_);
v___x_3661_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
lean_object* v___x_3662_; lean_object* v___x_3664_; 
v___x_3662_ = lean_st_ref_put(v_a_3604_, v___x_3661_);
if (v_isShared_3648_ == 0)
{
lean_ctor_set(v___x_3647_, 0, v_a_3639_);
v___x_3664_ = v___x_3647_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3639_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
lean_dec(v_a_3639_);
lean_dec_ref(v_e_3603_);
v_a_3670_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3645_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3645_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
}
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
lean_dec_ref(v_e_3603_);
v_a_3680_ = lean_ctor_get(v_r_3638_, 0);
lean_inc(v_a_3680_);
lean_dec_ref_known(v_r_3638_, 1);
v___x_3681_ = lean_box(0);
v___x_3682_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(v_a_3604_, v_visited_3625_, v_types_3626_, v_subst_3627_, v___x_3681_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; 
v_unused_3690_ = lean_ctor_get(v___x_3682_, 0);
lean_dec(v_unused_3690_);
v___x_3684_ = v___x_3682_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_dec(v___x_3682_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
lean_ctor_set_tag(v___x_3684_, 1);
lean_ctor_set(v___x_3684_, 0, v_a_3680_);
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3680_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_dec(v_a_3680_);
v_a_3691_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3682_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3682_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(lean_object* v_e_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_){
_start:
{
lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; uint8_t v___y_3759_; 
switch(lean_obj_tag(v_e_3701_))
{
case 0:
{
lean_object* v___x_3778_; 
v___x_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3778_, 0, v_e_3701_);
return v___x_3778_;
}
case 1:
{
lean_object* v___x_3779_; 
v___x_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3779_, 0, v_e_3701_);
return v___x_3779_;
}
case 2:
{
lean_object* v___x_3780_; 
v___x_3780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3780_, 0, v_e_3701_);
return v___x_3780_;
}
case 3:
{
lean_object* v___x_3781_; 
v___x_3781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3781_, 0, v_e_3701_);
return v___x_3781_;
}
case 4:
{
lean_object* v___x_3782_; 
v___x_3782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3782_, 0, v_e_3701_);
return v___x_3782_;
}
case 9:
{
lean_object* v___x_3783_; 
v___x_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3783_, 0, v_e_3701_);
return v___x_3783_;
}
default: 
{
lean_object* v_numCandidates_3784_; lean_object* v_cleanSuffix_3785_; lean_object* v___x_3786_; uint8_t v___x_3787_; 
v_numCandidates_3784_ = lean_ctor_get(v_a_3702_, 1);
v_cleanSuffix_3785_ = lean_ctor_get(v_a_3702_, 2);
v___x_3786_ = lean_unsigned_to_nat(0u);
v___x_3787_ = lean_nat_dec_eq(v_numCandidates_3784_, v___x_3786_);
if (v___x_3787_ == 0)
{
lean_object* v___x_3788_; uint8_t v___x_3789_; 
v___x_3788_ = l_Lean_Expr_looseBVarRange(v_e_3701_);
v___x_3789_ = lean_nat_dec_le(v___x_3788_, v_cleanSuffix_3785_);
lean_dec(v___x_3788_);
v___y_3759_ = v___x_3789_;
goto v___jp_3758_;
}
else
{
v___y_3759_ = v___x_3787_;
goto v___jp_3758_;
}
}
}
v___jp_3711_:
{
uint8_t v___x_3720_; 
v___x_3720_ = l_Lean_Expr_hasLooseBVars(v_e_3701_);
if (v___x_3720_ == 0)
{
lean_object* v___x_3721_; 
v___x_3721_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(v_e_3701_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_);
return v___x_3721_;
}
else
{
lean_object* v___x_3722_; lean_object* v_visited_3723_; lean_object* v___x_3724_; 
v___x_3722_ = lean_st_ref_get(v___y_3713_);
v_visited_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc_ref(v_visited_3723_);
lean_dec(v___x_3722_);
v___x_3724_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_visited_3723_, v_e_3701_);
lean_dec_ref(v_visited_3723_);
if (lean_obj_tag(v___x_3724_) == 1)
{
lean_object* v_val_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
lean_dec_ref(v_e_3701_);
v_val_3725_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___x_3724_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_val_3725_);
lean_dec(v___x_3724_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
lean_ctor_set_tag(v___x_3727_, 0);
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_val_3725_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
else
{
lean_object* v___x_3733_; 
lean_dec(v___x_3724_);
lean_inc_ref(v_e_3701_);
v___x_3733_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(v_e_3701_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3757_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3736_ = v___x_3733_;
v_isShared_3737_ = v_isSharedCheck_3757_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3733_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3757_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3738_; lean_object* v_visited_3739_; lean_object* v_types_3740_; lean_object* v_subst_3741_; lean_object* v_visitedClosed_3742_; lean_object* v_hasDepLetCache_3743_; lean_object* v_numConverted_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3756_; 
v___x_3738_ = lean_st_ref_take(v___y_3713_);
v_visited_3739_ = lean_ctor_get(v___x_3738_, 0);
v_types_3740_ = lean_ctor_get(v___x_3738_, 1);
v_subst_3741_ = lean_ctor_get(v___x_3738_, 2);
v_visitedClosed_3742_ = lean_ctor_get(v___x_3738_, 3);
v_hasDepLetCache_3743_ = lean_ctor_get(v___x_3738_, 4);
v_numConverted_3744_ = lean_ctor_get(v___x_3738_, 5);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3746_ = v___x_3738_;
v_isShared_3747_ = v_isSharedCheck_3756_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_numConverted_3744_);
lean_inc(v_hasDepLetCache_3743_);
lean_inc(v_visitedClosed_3742_);
lean_inc(v_subst_3741_);
lean_inc(v_types_3740_);
lean_inc(v_visited_3739_);
lean_dec(v___x_3738_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3756_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3748_; lean_object* v___x_3750_; 
lean_inc(v_a_3734_);
v___x_3748_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_visited_3739_, v_e_3701_, v_a_3734_);
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 0, v___x_3748_);
v___x_3750_ = v___x_3746_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3748_);
lean_ctor_set(v_reuseFailAlloc_3755_, 1, v_types_3740_);
lean_ctor_set(v_reuseFailAlloc_3755_, 2, v_subst_3741_);
lean_ctor_set(v_reuseFailAlloc_3755_, 3, v_visitedClosed_3742_);
lean_ctor_set(v_reuseFailAlloc_3755_, 4, v_hasDepLetCache_3743_);
lean_ctor_set(v_reuseFailAlloc_3755_, 5, v_numConverted_3744_);
v___x_3750_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
lean_object* v___x_3751_; lean_object* v___x_3753_; 
v___x_3751_ = lean_st_ref_put(v___y_3713_, v___x_3750_);
if (v_isShared_3737_ == 0)
{
v___x_3753_ = v___x_3736_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3734_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3701_);
return v___x_3733_;
}
}
}
}
v___jp_3758_:
{
if (v___y_3759_ == 0)
{
v___y_3712_ = v_a_3702_;
v___y_3713_ = v_a_3703_;
v___y_3714_ = v_a_3704_;
v___y_3715_ = v_a_3705_;
v___y_3716_ = v_a_3706_;
v___y_3717_ = v_a_3707_;
v___y_3718_ = v_a_3708_;
v___y_3719_ = v_a_3709_;
goto v___jp_3711_;
}
else
{
lean_object* v___x_3760_; 
lean_inc_ref(v_e_3701_);
v___x_3760_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_e_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3769_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3763_ = v___x_3760_;
v_isShared_3764_ = v_isSharedCheck_3769_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3769_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
uint8_t v___x_3765_; 
v___x_3765_ = lean_unbox(v_a_3761_);
lean_dec(v_a_3761_);
if (v___x_3765_ == 0)
{
lean_object* v___x_3767_; 
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 0, v_e_3701_);
v___x_3767_ = v___x_3763_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_e_3701_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
else
{
lean_del_object(v___x_3763_);
v___y_3712_ = v_a_3702_;
v___y_3713_ = v_a_3703_;
v___y_3714_ = v_a_3704_;
v___y_3715_ = v_a_3705_;
v___y_3716_ = v_a_3706_;
v___y_3717_ = v_a_3707_;
v___y_3718_ = v_a_3708_;
v___y_3719_ = v_a_3709_;
goto v___jp_3711_;
}
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
lean_dec_ref(v_e_3701_);
v_a_3770_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3760_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3760_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0(lean_object* v_body_3790_, lean_object* v_binderName_3791_, uint8_t v_binderInfo_3792_, lean_object* v_a_3793_, lean_object* v_e_3794_, lean_object* v_binderType_3795_, lean_object* v_x_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v___x_3806_; 
lean_inc_ref(v_body_3790_);
v___x_3806_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_body_3790_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3823_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3809_ = v___x_3806_;
v_isShared_3810_ = v_isSharedCheck_3823_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3806_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3823_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
uint8_t v___y_3812_; size_t v___x_3817_; size_t v___x_3818_; uint8_t v___x_3819_; 
v___x_3817_ = lean_ptr_addr(v_binderType_3795_);
v___x_3818_ = lean_ptr_addr(v_a_3793_);
v___x_3819_ = lean_usize_dec_eq(v___x_3817_, v___x_3818_);
if (v___x_3819_ == 0)
{
lean_dec_ref(v_body_3790_);
v___y_3812_ = v___x_3819_;
goto v___jp_3811_;
}
else
{
size_t v___x_3820_; size_t v___x_3821_; uint8_t v___x_3822_; 
v___x_3820_ = lean_ptr_addr(v_body_3790_);
lean_dec_ref(v_body_3790_);
v___x_3821_ = lean_ptr_addr(v_a_3807_);
v___x_3822_ = lean_usize_dec_eq(v___x_3820_, v___x_3821_);
v___y_3812_ = v___x_3822_;
goto v___jp_3811_;
}
v___jp_3811_:
{
if (v___y_3812_ == 0)
{
lean_object* v___x_3813_; 
lean_del_object(v___x_3809_);
lean_dec_ref(v_e_3794_);
v___x_3813_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(v_binderName_3791_, v_binderInfo_3792_, v_a_3793_, v_a_3807_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
return v___x_3813_;
}
else
{
lean_object* v___x_3815_; 
lean_dec(v_a_3807_);
lean_dec_ref(v_a_3793_);
lean_dec(v_binderName_3791_);
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 0, v_e_3794_);
v___x_3815_ = v___x_3809_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_e_3794_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3794_);
lean_dec_ref(v_a_3793_);
lean_dec(v_binderName_3791_);
lean_dec_ref(v_body_3790_);
return v___x_3806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___boxed(lean_object* v_e_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_){
_start:
{
lean_object* v_res_3833_; 
v_res_3833_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(v_e_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_);
lean_dec(v_a_3831_);
lean_dec_ref(v_a_3830_);
lean_dec(v_a_3829_);
lean_dec_ref(v_a_3828_);
lean_dec(v_a_3827_);
lean_dec_ref(v_a_3826_);
lean_dec(v_a_3825_);
return v_res_3833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___boxed(lean_object* v_e_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(v_e_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_);
lean_dec(v_a_3842_);
lean_dec_ref(v_a_3841_);
lean_dec(v_a_3840_);
lean_dec_ref(v_a_3839_);
lean_dec(v_a_3838_);
lean_dec_ref(v_a_3837_);
lean_dec(v_a_3836_);
lean_dec_ref(v_a_3835_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit___boxed(lean_object* v_e_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_e_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_);
lean_dec(v_a_3853_);
lean_dec_ref(v_a_3852_);
lean_dec(v_a_3851_);
lean_dec_ref(v_a_3850_);
lean_dec(v_a_3849_);
lean_dec_ref(v_a_3848_);
lean_dec(v_a_3847_);
lean_dec_ref(v_a_3846_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___boxed(lean_object* v_e_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(v_e_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_);
lean_dec(v_a_3864_);
lean_dec_ref(v_a_3863_);
lean_dec(v_a_3862_);
lean_dec_ref(v_a_3861_);
lean_dec(v_a_3860_);
lean_dec_ref(v_a_3859_);
lean_dec(v_a_3858_);
lean_dec_ref(v_a_3857_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1(lean_object* v_f_3867_, lean_object* v_a_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
lean_object* v___x_3878_; 
v___x_3878_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(v_f_3867_, v_a_3868_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
return v___x_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___boxed(lean_object* v_f_3879_, lean_object* v_a_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1(v_f_3879_, v_a_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3881_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2(lean_object* v_d_3891_, lean_object* v_e_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v___x_3902_; 
v___x_3902_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(v_d_3891_, v_e_3892_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___boxed(lean_object* v_d_3903_, lean_object* v_e_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2(v_d_3903_, v_e_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_);
lean_dec(v___y_3912_);
lean_dec_ref(v___y_3911_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3(lean_object* v_structName_3915_, lean_object* v_idx_3916_, lean_object* v_struct_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
lean_object* v___x_3927_; 
v___x_3927_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(v_structName_3915_, v_idx_3916_, v_struct_3917_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___boxed(lean_object* v_structName_3928_, lean_object* v_idx_3929_, lean_object* v_struct_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v_res_3940_; 
v_res_3940_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3(v_structName_3928_, v_idx_3929_, v_struct_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
lean_dec(v___y_3934_);
lean_dec_ref(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4(lean_object* v_x_3941_, uint8_t v_bi_3942_, lean_object* v_t_3943_, lean_object* v_b_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
lean_object* v___x_3954_; 
v___x_3954_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(v_x_3941_, v_bi_3942_, v_t_3943_, v_b_3944_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___boxed(lean_object* v_x_3955_, lean_object* v_bi_3956_, lean_object* v_t_3957_, lean_object* v_b_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
uint8_t v_bi_boxed_3968_; lean_object* v_res_3969_; 
v_bi_boxed_3968_ = lean_unbox(v_bi_3956_);
v_res_3969_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4(v_x_3955_, v_bi_boxed_3968_, v_t_3957_, v_b_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3959_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5(lean_object* v_x_3970_, lean_object* v_t_3971_, lean_object* v_v_3972_, lean_object* v_b_3973_, uint8_t v_nondep_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v___x_3984_; 
v___x_3984_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_x_3970_, v_t_3971_, v_v_3972_, v_b_3973_, v_nondep_3974_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
return v___x_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___boxed(lean_object* v_x_3985_, lean_object* v_t_3986_, lean_object* v_v_3987_, lean_object* v_b_3988_, lean_object* v_nondep_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_){
_start:
{
uint8_t v_nondep_boxed_3999_; lean_object* v_res_4000_; 
v_nondep_boxed_3999_ = lean_unbox(v_nondep_3989_);
v_res_4000_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5(v_x_3985_, v_t_3986_, v_v_3987_, v_b_3988_, v_nondep_boxed_3999_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
lean_dec(v___y_3997_);
lean_dec_ref(v___y_3996_);
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
lean_dec(v___y_3991_);
lean_dec_ref(v___y_3990_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8(lean_object* v_x_4001_, uint8_t v_bi_4002_, lean_object* v_t_4003_, lean_object* v_b_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v___x_4014_; 
v___x_4014_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(v_x_4001_, v_bi_4002_, v_t_4003_, v_b_4004_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
return v___x_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___boxed(lean_object* v_x_4015_, lean_object* v_bi_4016_, lean_object* v_t_4017_, lean_object* v_b_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
uint8_t v_bi_boxed_4028_; lean_object* v_res_4029_; 
v_bi_boxed_4028_ = lean_unbox(v_bi_4016_);
v_res_4029_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8(v_x_4015_, v_bi_boxed_4028_, v_t_4017_, v_b_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed(lean_object* v_e_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_){
_start:
{
lean_object* v___x_4040_; 
v___x_4040_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(v_e_4030_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_);
return v___x_4040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___boxed(lean_object* v_e_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_){
_start:
{
lean_object* v_res_4051_; 
v_res_4051_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed(v_e_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_);
lean_dec(v_a_4049_);
lean_dec_ref(v_a_4048_);
lean_dec(v_a_4047_);
lean_dec_ref(v_a_4046_);
lean_dec(v_a_4045_);
lean_dec_ref(v_a_4044_);
lean_dec(v_a_4043_);
lean_dec_ref(v_a_4042_);
return v_res_4051_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6(lean_object* v_00_u03b2_4052_, lean_object* v_k_4053_, lean_object* v_t_4054_){
_start:
{
uint8_t v___x_4055_; 
v___x_4055_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(v_k_4053_, v_t_4054_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___boxed(lean_object* v_00_u03b2_4056_, lean_object* v_k_4057_, lean_object* v_t_4058_){
_start:
{
uint8_t v_res_4059_; lean_object* v_r_4060_; 
v_res_4059_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6(v_00_u03b2_4056_, v_k_4057_, v_t_4058_);
lean_dec(v_t_4058_);
lean_dec(v_k_4057_);
v_r_4060_ = lean_box(v_res_4059_);
return v_r_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0(lean_object* v_x_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
lean_object* v___x_4069_; 
lean_inc(v___y_4063_);
lean_inc_ref(v___y_4062_);
v___x_4069_ = lean_apply_7(v_x_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, lean_box(0));
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0___boxed(lean_object* v_x_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0(v_x_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(lean_object* v_lctx_4079_, lean_object* v_localInsts_4080_, lean_object* v_x_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_){
_start:
{
lean_object* v___f_4089_; lean_object* v___x_4090_; 
lean_inc(v___y_4083_);
lean_inc_ref(v___y_4082_);
v___f_4089_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4089_, 0, v_x_4081_);
lean_closure_set(v___f_4089_, 1, v___y_4082_);
lean_closure_set(v___f_4089_, 2, v___y_4083_);
v___x_4090_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4079_, v_localInsts_4080_, v___f_4089_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_);
if (lean_obj_tag(v___x_4090_) == 0)
{
return v___x_4090_;
}
else
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4098_; 
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4093_ = v___x_4090_;
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v___x_4090_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4096_; 
if (v_isShared_4094_ == 0)
{
v___x_4096_ = v___x_4093_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4091_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___boxed(lean_object* v_lctx_4099_, lean_object* v_localInsts_4100_, lean_object* v_x_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(v_lctx_4099_, v_localInsts_4100_, v_x_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
lean_dec(v___y_4105_);
lean_dec_ref(v___y_4104_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0(lean_object* v_00_u03b1_4110_, lean_object* v_lctx_4111_, lean_object* v_localInsts_4112_, lean_object* v_x_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v___x_4121_; 
v___x_4121_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(v_lctx_4111_, v_localInsts_4112_, v_x_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
return v___x_4121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___boxed(lean_object* v_00_u03b1_4122_, lean_object* v_lctx_4123_, lean_object* v_localInsts_4124_, lean_object* v_x_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_){
_start:
{
lean_object* v_res_4133_; 
v_res_4133_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0(v_00_u03b1_4122_, v_lctx_4123_, v_localInsts_4124_, v_x_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0(lean_object* v_k_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_){
_start:
{
lean_object* v___x_4142_; 
lean_inc(v___y_4136_);
lean_inc_ref(v___y_4135_);
v___x_4142_ = lean_apply_7(v_k_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, lean_box(0));
return v___x_4142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0___boxed(lean_object* v_k_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_){
_start:
{
lean_object* v_res_4151_; 
v_res_4151_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0(v_k_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg(lean_object* v_k_4152_, uint8_t v_allowLevelAssignments_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v___f_4161_; lean_object* v___x_4162_; 
lean_inc(v___y_4155_);
lean_inc_ref(v___y_4154_);
v___f_4161_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4161_, 0, v_k_4152_);
lean_closure_set(v___f_4161_, 1, v___y_4154_);
lean_closure_set(v___f_4161_, 2, v___y_4155_);
v___x_4162_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_4153_, v___f_4161_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
if (lean_obj_tag(v___x_4162_) == 0)
{
return v___x_4162_;
}
else
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4170_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4170_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4165_ = v___x_4162_;
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v___x_4162_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4168_; 
if (v_isShared_4166_ == 0)
{
v___x_4168_ = v___x_4165_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v_a_4163_);
v___x_4168_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
return v___x_4168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___boxed(lean_object* v_k_4171_, lean_object* v_allowLevelAssignments_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_4180_; lean_object* v_res_4181_; 
v_allowLevelAssignments_boxed_4180_ = lean_unbox(v_allowLevelAssignments_4172_);
v_res_4181_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg(v_k_4171_, v_allowLevelAssignments_boxed_4180_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1(lean_object* v_00_u03b1_4182_, lean_object* v_k_4183_, uint8_t v_allowLevelAssignments_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg(v_k_4183_, v_allowLevelAssignments_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___boxed(lean_object* v_00_u03b1_4193_, lean_object* v_k_4194_, lean_object* v_allowLevelAssignments_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_4203_; lean_object* v_res_4204_; 
v_allowLevelAssignments_boxed_4203_ = lean_unbox(v_allowLevelAssignments_4195_);
v_res_4204_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1(v_00_u03b1_4193_, v_k_4194_, v_allowLevelAssignments_boxed_4203_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
return v_res_4204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__0(lean_object* v___y_4205_, lean_object* v_zetaDeltaFVarIds_4206_, lean_object* v_a_x3f_4207_){
_start:
{
lean_object* v___x_4209_; lean_object* v_mctx_4210_; lean_object* v_cache_4211_; lean_object* v_postponed_4212_; lean_object* v_diag_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4223_; 
v___x_4209_ = lean_st_ref_take(v___y_4205_);
v_mctx_4210_ = lean_ctor_get(v___x_4209_, 0);
v_cache_4211_ = lean_ctor_get(v___x_4209_, 1);
v_postponed_4212_ = lean_ctor_get(v___x_4209_, 3);
v_diag_4213_ = lean_ctor_get(v___x_4209_, 4);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4223_ == 0)
{
lean_object* v_unused_4224_; 
v_unused_4224_ = lean_ctor_get(v___x_4209_, 2);
lean_dec(v_unused_4224_);
v___x_4215_ = v___x_4209_;
v_isShared_4216_ = v_isSharedCheck_4223_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_diag_4213_);
lean_inc(v_postponed_4212_);
lean_inc(v_cache_4211_);
lean_inc(v_mctx_4210_);
lean_dec(v___x_4209_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4223_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4218_; 
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 2, v_zetaDeltaFVarIds_4206_);
v___x_4218_ = v___x_4215_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_mctx_4210_);
lean_ctor_set(v_reuseFailAlloc_4222_, 1, v_cache_4211_);
lean_ctor_set(v_reuseFailAlloc_4222_, 2, v_zetaDeltaFVarIds_4206_);
lean_ctor_set(v_reuseFailAlloc_4222_, 3, v_postponed_4212_);
lean_ctor_set(v_reuseFailAlloc_4222_, 4, v_diag_4213_);
v___x_4218_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___x_4219_ = lean_st_ref_put(v___y_4205_, v___x_4218_);
v___x_4220_ = lean_box(0);
v___x_4221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4220_);
return v___x_4221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__0___boxed(lean_object* v___y_4225_, lean_object* v_zetaDeltaFVarIds_4226_, lean_object* v_a_x3f_4227_, lean_object* v___y_4228_){
_start:
{
lean_object* v_res_4229_; 
v_res_4229_ = l_Lean_Meta_Sym_letToHave___lam__0(v___y_4225_, v_zetaDeltaFVarIds_4226_, v_a_x3f_4227_);
lean_dec(v_a_x3f_4227_);
lean_dec(v___y_4225_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__1(lean_object* v___y_4230_, lean_object* v_cache_4231_, lean_object* v_a_x3f_4232_){
_start:
{
lean_object* v___x_4234_; lean_object* v_mctx_4235_; lean_object* v_zetaDeltaFVarIds_4236_; lean_object* v_postponed_4237_; lean_object* v_diag_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4248_; 
v___x_4234_ = lean_st_ref_take(v___y_4230_);
v_mctx_4235_ = lean_ctor_get(v___x_4234_, 0);
v_zetaDeltaFVarIds_4236_ = lean_ctor_get(v___x_4234_, 2);
v_postponed_4237_ = lean_ctor_get(v___x_4234_, 3);
v_diag_4238_ = lean_ctor_get(v___x_4234_, 4);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4234_);
if (v_isSharedCheck_4248_ == 0)
{
lean_object* v_unused_4249_; 
v_unused_4249_ = lean_ctor_get(v___x_4234_, 1);
lean_dec(v_unused_4249_);
v___x_4240_ = v___x_4234_;
v_isShared_4241_ = v_isSharedCheck_4248_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_diag_4238_);
lean_inc(v_postponed_4237_);
lean_inc(v_zetaDeltaFVarIds_4236_);
lean_inc(v_mctx_4235_);
lean_dec(v___x_4234_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4248_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4243_; 
if (v_isShared_4241_ == 0)
{
lean_ctor_set(v___x_4240_, 1, v_cache_4231_);
v___x_4243_ = v___x_4240_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_mctx_4235_);
lean_ctor_set(v_reuseFailAlloc_4247_, 1, v_cache_4231_);
lean_ctor_set(v_reuseFailAlloc_4247_, 2, v_zetaDeltaFVarIds_4236_);
lean_ctor_set(v_reuseFailAlloc_4247_, 3, v_postponed_4237_);
lean_ctor_set(v_reuseFailAlloc_4247_, 4, v_diag_4238_);
v___x_4243_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4244_ = lean_st_ref_put(v___y_4230_, v___x_4243_);
v___x_4245_ = lean_box(0);
v___x_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4245_);
return v___x_4246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__1___boxed(lean_object* v___y_4250_, lean_object* v_cache_4251_, lean_object* v_a_x3f_4252_, lean_object* v___y_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l_Lean_Meta_Sym_letToHave___lam__1(v___y_4250_, v_cache_4251_, v_a_x3f_4252_);
lean_dec(v_a_x3f_4252_);
lean_dec(v___y_4250_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__2(lean_object* v___x_4255_, lean_object* v_e_4256_, lean_object* v___x_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v___x_4265_; lean_object* v_a_4267_; lean_object* v___x_4270_; 
v___x_4265_ = lean_st_mk_ref(v___x_4255_);
lean_inc_ref(v_e_4256_);
v___x_4270_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_e_4256_, v___x_4257_, v___x_4265_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_);
if (lean_obj_tag(v___x_4270_) == 0)
{
lean_object* v_a_4271_; uint8_t v___x_4272_; 
v_a_4271_ = lean_ctor_get(v___x_4270_, 0);
lean_inc(v_a_4271_);
lean_dec_ref_known(v___x_4270_, 1);
v___x_4272_ = lean_unbox(v_a_4271_);
lean_dec(v_a_4271_);
if (v___x_4272_ == 0)
{
v_a_4267_ = v_e_4256_;
goto v___jp_4266_;
}
else
{
lean_object* v___x_4273_; 
v___x_4273_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_e_4256_, v___x_4257_, v___x_4265_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v_a_4274_; 
v_a_4274_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_a_4274_);
lean_dec_ref_known(v___x_4273_, 1);
v_a_4267_ = v_a_4274_;
goto v___jp_4266_;
}
else
{
lean_dec(v___x_4265_);
return v___x_4273_;
}
}
}
else
{
lean_object* v_a_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4282_; 
lean_dec(v___x_4265_);
lean_dec_ref(v_e_4256_);
v_a_4275_ = lean_ctor_get(v___x_4270_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4277_ = v___x_4270_;
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_a_4275_);
lean_dec(v___x_4270_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4280_; 
if (v_isShared_4278_ == 0)
{
v___x_4280_ = v___x_4277_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4275_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
v___jp_4266_:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4268_ = lean_st_ref_get(v___x_4265_);
lean_dec(v___x_4265_);
lean_dec(v___x_4268_);
v___x_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4269_, 0, v_a_4267_);
return v___x_4269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__2___boxed(lean_object* v___x_4283_, lean_object* v_e_4284_, lean_object* v___x_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_){
_start:
{
lean_object* v_res_4293_; 
v_res_4293_ = l_Lean_Meta_Sym_letToHave___lam__2(v___x_4283_, v_e_4284_, v___x_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec_ref(v___x_4285_);
return v_res_4293_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___lam__3___closed__0(void){
_start:
{
lean_object* v___x_4294_; 
v___x_4294_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4294_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___lam__3___closed__1(void){
_start:
{
lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4295_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__3___closed__0, &l_Lean_Meta_Sym_letToHave___lam__3___closed__0_once, _init_l_Lean_Meta_Sym_letToHave___lam__3___closed__0);
v___x_4296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4295_);
return v___x_4296_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___lam__3___closed__2(void){
_start:
{
lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4297_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__3___closed__1, &l_Lean_Meta_Sym_letToHave___lam__3___closed__1_once, _init_l_Lean_Meta_Sym_letToHave___lam__3___closed__1);
v___x_4298_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4297_);
lean_ctor_set(v___x_4298_, 1, v___x_4297_);
lean_ctor_set(v___x_4298_, 2, v___x_4297_);
lean_ctor_set(v___x_4298_, 3, v___x_4297_);
lean_ctor_set(v___x_4298_, 4, v___x_4297_);
lean_ctor_set(v___x_4298_, 5, v___x_4297_);
return v___x_4298_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___lam__3___closed__3(void){
_start:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v___x_4299_ = lean_unsigned_to_nat(0u);
v___x_4300_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1);
v___x_4301_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4300_);
lean_ctor_set(v___x_4301_, 1, v___x_4300_);
lean_ctor_set(v___x_4301_, 2, v___x_4300_);
lean_ctor_set(v___x_4301_, 3, v___x_4300_);
lean_ctor_set(v___x_4301_, 4, v___x_4300_);
lean_ctor_set(v___x_4301_, 5, v___x_4299_);
return v___x_4301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__3(uint8_t v___x_4302_, lean_object* v_e_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_){
_start:
{
lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v_mctx_4313_; lean_object* v_zetaDeltaFVarIds_4314_; lean_object* v_postponed_4315_; lean_object* v_diag_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4418_; 
v___x_4311_ = lean_st_ref_get(v___y_4307_);
v___x_4312_ = lean_st_ref_take(v___y_4307_);
v_mctx_4313_ = lean_ctor_get(v___x_4312_, 0);
v_zetaDeltaFVarIds_4314_ = lean_ctor_get(v___x_4312_, 2);
v_postponed_4315_ = lean_ctor_get(v___x_4312_, 3);
v_diag_4316_ = lean_ctor_get(v___x_4312_, 4);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4418_ == 0)
{
lean_object* v_unused_4419_; 
v_unused_4419_ = lean_ctor_get(v___x_4312_, 1);
lean_dec(v_unused_4419_);
v___x_4318_ = v___x_4312_;
v_isShared_4319_ = v_isSharedCheck_4418_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_diag_4316_);
lean_inc(v_postponed_4315_);
lean_inc(v_zetaDeltaFVarIds_4314_);
lean_inc(v_mctx_4313_);
lean_dec(v___x_4312_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4418_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4320_; lean_object* v___x_4322_; 
v___x_4320_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__3___closed__2, &l_Lean_Meta_Sym_letToHave___lam__3___closed__2_once, _init_l_Lean_Meta_Sym_letToHave___lam__3___closed__2);
if (v_isShared_4319_ == 0)
{
lean_ctor_set(v___x_4318_, 1, v___x_4320_);
v___x_4322_ = v___x_4318_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_mctx_4313_);
lean_ctor_set(v_reuseFailAlloc_4417_, 1, v___x_4320_);
lean_ctor_set(v_reuseFailAlloc_4417_, 2, v_zetaDeltaFVarIds_4314_);
lean_ctor_set(v_reuseFailAlloc_4417_, 3, v_postponed_4315_);
lean_ctor_set(v_reuseFailAlloc_4417_, 4, v_diag_4316_);
v___x_4322_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v_mctx_4325_; lean_object* v_cache_4326_; lean_object* v_zetaDeltaFVarIds_4327_; lean_object* v_postponed_4328_; lean_object* v_diag_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4416_; 
v___x_4323_ = lean_st_ref_put(v___y_4307_, v___x_4322_);
v___x_4324_ = lean_st_ref_take(v___y_4307_);
v_mctx_4325_ = lean_ctor_get(v___x_4324_, 0);
v_cache_4326_ = lean_ctor_get(v___x_4324_, 1);
v_zetaDeltaFVarIds_4327_ = lean_ctor_get(v___x_4324_, 2);
v_postponed_4328_ = lean_ctor_get(v___x_4324_, 3);
v_diag_4329_ = lean_ctor_get(v___x_4324_, 4);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4331_ = v___x_4324_;
v_isShared_4332_ = v_isSharedCheck_4416_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_diag_4329_);
lean_inc(v_postponed_4328_);
lean_inc(v_zetaDeltaFVarIds_4327_);
lean_inc(v_cache_4326_);
lean_inc(v_mctx_4325_);
lean_dec(v___x_4324_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4416_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4333_; lean_object* v___x_4335_; 
v___x_4333_ = lean_box(1);
if (v_isShared_4332_ == 0)
{
lean_ctor_set(v___x_4331_, 2, v___x_4333_);
v___x_4335_ = v___x_4331_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_mctx_4325_);
lean_ctor_set(v_reuseFailAlloc_4415_, 1, v_cache_4326_);
lean_ctor_set(v_reuseFailAlloc_4415_, 2, v___x_4333_);
lean_ctor_set(v_reuseFailAlloc_4415_, 3, v_postponed_4328_);
lean_ctor_set(v_reuseFailAlloc_4415_, 4, v_diag_4329_);
v___x_4335_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
lean_object* v___x_4336_; lean_object* v_cache_4337_; lean_object* v_keyedConfig_4338_; lean_object* v_zetaDeltaSet_4339_; lean_object* v_lctx_4340_; lean_object* v_localInstances_4341_; lean_object* v_defEqCtx_x3f_4342_; lean_object* v_synthPendingDepth_4343_; lean_object* v_customCanUnfoldPredicate_x3f_4344_; uint8_t v_univApprox_4345_; uint8_t v_inTypeClassResolution_4346_; uint8_t v_cacheInferType_4347_; uint8_t v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; uint8_t v_foApprox_4352_; uint8_t v_ctxApprox_4353_; uint8_t v_quasiPatternApprox_4354_; uint8_t v_constApprox_4355_; uint8_t v_isDefEqStuckEx_4356_; uint8_t v_unificationHints_4357_; uint8_t v_proofIrrelevance_4358_; uint8_t v_assignSyntheticOpaque_4359_; uint8_t v_offsetCnstrs_4360_; uint8_t v_transparency_4361_; uint8_t v_univApprox_4362_; uint8_t v_zetaUnused_4363_; uint8_t v_canUnfoldPredicateConfig_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4414_; 
v___x_4336_ = lean_st_ref_put(v___y_4307_, v___x_4335_);
v_cache_4337_ = lean_ctor_get(v___x_4311_, 1);
lean_inc_ref(v_cache_4337_);
lean_dec(v___x_4311_);
v_keyedConfig_4338_ = lean_ctor_get(v___y_4306_, 0);
v_zetaDeltaSet_4339_ = lean_ctor_get(v___y_4306_, 1);
v_lctx_4340_ = lean_ctor_get(v___y_4306_, 2);
v_localInstances_4341_ = lean_ctor_get(v___y_4306_, 3);
v_defEqCtx_x3f_4342_ = lean_ctor_get(v___y_4306_, 4);
v_synthPendingDepth_4343_ = lean_ctor_get(v___y_4306_, 5);
v_customCanUnfoldPredicate_x3f_4344_ = lean_ctor_get(v___y_4306_, 6);
v_univApprox_4345_ = lean_ctor_get_uint8(v___y_4306_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4346_ = lean_ctor_get_uint8(v___y_4306_, sizeof(void*)*7 + 2);
v_cacheInferType_4347_ = lean_ctor_get_uint8(v___y_4306_, sizeof(void*)*7 + 3);
v___x_4348_ = 1;
lean_inc_ref(v_keyedConfig_4338_);
v___x_4349_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4302_, v_keyedConfig_4338_);
lean_inc(v_customCanUnfoldPredicate_x3f_4344_);
lean_inc(v_synthPendingDepth_4343_);
lean_inc(v_defEqCtx_x3f_4342_);
lean_inc_ref(v_localInstances_4341_);
lean_inc_ref(v_lctx_4340_);
lean_inc(v_zetaDeltaSet_4339_);
v___x_4350_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4350_, 0, v___x_4349_);
lean_ctor_set(v___x_4350_, 1, v_zetaDeltaSet_4339_);
lean_ctor_set(v___x_4350_, 2, v_lctx_4340_);
lean_ctor_set(v___x_4350_, 3, v_localInstances_4341_);
lean_ctor_set(v___x_4350_, 4, v_defEqCtx_x3f_4342_);
lean_ctor_set(v___x_4350_, 5, v_synthPendingDepth_4343_);
lean_ctor_set(v___x_4350_, 6, v_customCanUnfoldPredicate_x3f_4344_);
lean_ctor_set_uint8(v___x_4350_, sizeof(void*)*7, v___x_4348_);
lean_ctor_set_uint8(v___x_4350_, sizeof(void*)*7 + 1, v_univApprox_4345_);
lean_ctor_set_uint8(v___x_4350_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4346_);
lean_ctor_set_uint8(v___x_4350_, sizeof(void*)*7 + 3, v_cacheInferType_4347_);
v___x_4351_ = l_Lean_Meta_Context_config(v___x_4350_);
lean_dec_ref_known(v___x_4350_, 7);
v_foApprox_4352_ = lean_ctor_get_uint8(v___x_4351_, 0);
v_ctxApprox_4353_ = lean_ctor_get_uint8(v___x_4351_, 1);
v_quasiPatternApprox_4354_ = lean_ctor_get_uint8(v___x_4351_, 2);
v_constApprox_4355_ = lean_ctor_get_uint8(v___x_4351_, 3);
v_isDefEqStuckEx_4356_ = lean_ctor_get_uint8(v___x_4351_, 4);
v_unificationHints_4357_ = lean_ctor_get_uint8(v___x_4351_, 5);
v_proofIrrelevance_4358_ = lean_ctor_get_uint8(v___x_4351_, 6);
v_assignSyntheticOpaque_4359_ = lean_ctor_get_uint8(v___x_4351_, 7);
v_offsetCnstrs_4360_ = lean_ctor_get_uint8(v___x_4351_, 8);
v_transparency_4361_ = lean_ctor_get_uint8(v___x_4351_, 9);
v_univApprox_4362_ = lean_ctor_get_uint8(v___x_4351_, 11);
v_zetaUnused_4363_ = lean_ctor_get_uint8(v___x_4351_, 17);
v_canUnfoldPredicateConfig_4364_ = lean_ctor_get_uint8(v___x_4351_, 19);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4366_ = v___x_4351_;
v_isShared_4367_ = v_isSharedCheck_4414_;
goto v_resetjp_4365_;
}
else
{
lean_dec(v___x_4351_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4414_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v_a_4369_; uint8_t v___x_4380_; uint8_t v___x_4381_; lean_object* v___x_4383_; 
v___x_4380_ = 0;
v___x_4381_ = 2;
if (v_isShared_4367_ == 0)
{
v___x_4383_ = v___x_4366_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4413_, 0, v_foApprox_4352_);
lean_ctor_set_uint8(v_reuseFailAlloc_4413_, 1, v_ctxApprox_4353_);
lean_ctor_set_uint8(v_reuseFailAlloc_4413_, 2, v_quasiPatternApprox_4354_);
lean_ctor_set_uint8(v_reuseFailAlloc_4413_, 3, v_constApprox_4355_);
lean_ctor_set_uint8(v_reuseFailAlloc_4413_, 4, v_isDefEqStuckEx_4356_);
lean_ctor_set_uint8(v_reuseFailAlloc_4413_, 5, v_unificationHints_4357_);
lean_ctor_set_uint8(v_reuseFailAlloc_4413_, 6, v_proofIrrelevance_4358_);
lean_ctor_set_uint8(v_reuseFailAlloc_4413_, 7, v_assignSyntheticOpaque_4359_);
lean_ctor_set_uint8(v_reuseFailAlloc_4413_, 8, v_offsetCnstrs_4360_);
lean_ctor_set_uint8(v_reuseFailAlloc_4413_, 9, v_transparency_4361_);
lean_ctor_set_uint8(v_reuseFailAlloc_4413_, 11, v_univApprox_4362_);
lean_ctor_set_uint8(v_reuseFailAlloc_4413_, 17, v_zetaUnused_4363_);
lean_ctor_set_uint8(v_reuseFailAlloc_4413_, 19, v_canUnfoldPredicateConfig_4364_);
v___x_4383_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4382_;
}
v___jp_4368_:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4378_; 
v___x_4370_ = lean_box(0);
v___x_4371_ = l_Lean_Meta_Sym_letToHave___lam__1(v___y_4307_, v_cache_4337_, v___x_4370_);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4378_ == 0)
{
lean_object* v_unused_4379_; 
v_unused_4379_ = lean_ctor_get(v___x_4371_, 0);
lean_dec(v_unused_4379_);
v___x_4373_ = v___x_4371_;
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
else
{
lean_dec(v___x_4371_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v___x_4376_; 
if (v_isShared_4374_ == 0)
{
lean_ctor_set_tag(v___x_4373_, 1);
lean_ctor_set(v___x_4373_, 0, v_a_4369_);
v___x_4376_ = v___x_4373_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_a_4369_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
return v___x_4376_;
}
}
}
v_reusejp_4382_:
{
uint64_t v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___f_4390_; lean_object* v___x_4391_; 
lean_ctor_set_uint8(v___x_4383_, 10, v___x_4380_);
lean_ctor_set_uint8(v___x_4383_, 12, v___x_4348_);
lean_ctor_set_uint8(v___x_4383_, 13, v___x_4348_);
lean_ctor_set_uint8(v___x_4383_, 14, v___x_4381_);
lean_ctor_set_uint8(v___x_4383_, 15, v___x_4348_);
lean_ctor_set_uint8(v___x_4383_, 16, v___x_4348_);
lean_ctor_set_uint8(v___x_4383_, 18, v___x_4348_);
v___x_4384_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4383_);
v___x_4385_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4385_, 0, v___x_4383_);
lean_ctor_set_uint64(v___x_4385_, sizeof(void*)*1, v___x_4384_);
lean_inc(v_customCanUnfoldPredicate_x3f_4344_);
lean_inc(v_synthPendingDepth_4343_);
lean_inc(v_defEqCtx_x3f_4342_);
lean_inc_ref(v_localInstances_4341_);
lean_inc_ref_n(v_lctx_4340_, 2);
lean_inc(v_zetaDeltaSet_4339_);
v___x_4386_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4386_, 0, v___x_4385_);
lean_ctor_set(v___x_4386_, 1, v_zetaDeltaSet_4339_);
lean_ctor_set(v___x_4386_, 2, v_lctx_4340_);
lean_ctor_set(v___x_4386_, 3, v_localInstances_4341_);
lean_ctor_set(v___x_4386_, 4, v_defEqCtx_x3f_4342_);
lean_ctor_set(v___x_4386_, 5, v_synthPendingDepth_4343_);
lean_ctor_set(v___x_4386_, 6, v_customCanUnfoldPredicate_x3f_4344_);
lean_ctor_set_uint8(v___x_4386_, sizeof(void*)*7, v___x_4348_);
lean_ctor_set_uint8(v___x_4386_, sizeof(void*)*7 + 1, v_univApprox_4345_);
lean_ctor_set_uint8(v___x_4386_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4346_);
lean_ctor_set_uint8(v___x_4386_, sizeof(void*)*7 + 3, v_cacheInferType_4347_);
v___x_4387_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___closed__0));
v___x_4388_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2);
v___x_4389_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__3___closed__3, &l_Lean_Meta_Sym_letToHave___lam__3___closed__3_once, _init_l_Lean_Meta_Sym_letToHave___lam__3___closed__3);
v___f_4390_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_letToHave___lam__2___boxed), 10, 3);
lean_closure_set(v___f_4390_, 0, v___x_4389_);
lean_closure_set(v___f_4390_, 1, v_e_4303_);
lean_closure_set(v___f_4390_, 2, v___x_4388_);
v___x_4391_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(v_lctx_4340_, v___x_4387_, v___f_4390_, v___y_4304_, v___y_4305_, v___x_4386_, v___y_4307_, v___y_4308_, v___y_4309_);
lean_dec_ref_known(v___x_4386_, 7);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v_a_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4409_; 
v_a_4392_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4394_ = v___x_4391_;
v_isShared_4395_ = v_isSharedCheck_4409_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_a_4392_);
lean_dec(v___x_4391_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4409_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4397_; 
lean_inc(v_a_4392_);
if (v_isShared_4395_ == 0)
{
lean_ctor_set_tag(v___x_4394_, 1);
v___x_4397_ = v___x_4394_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_a_4392_);
v___x_4397_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4406_; 
v___x_4398_ = l_Lean_Meta_Sym_letToHave___lam__0(v___y_4307_, v_zetaDeltaFVarIds_4327_, v___x_4397_);
lean_dec_ref(v___x_4398_);
v___x_4399_ = l_Lean_Meta_Sym_letToHave___lam__1(v___y_4307_, v_cache_4337_, v___x_4397_);
lean_dec_ref(v___x_4397_);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4399_);
if (v_isSharedCheck_4406_ == 0)
{
lean_object* v_unused_4407_; 
v_unused_4407_ = lean_ctor_get(v___x_4399_, 0);
lean_dec(v_unused_4407_);
v___x_4401_ = v___x_4399_;
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
else
{
lean_dec(v___x_4399_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4404_; 
if (v_isShared_4402_ == 0)
{
lean_ctor_set(v___x_4401_, 0, v_a_4392_);
v___x_4404_ = v___x_4401_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4392_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
return v___x_4404_;
}
}
}
}
}
else
{
lean_object* v_a_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
v_a_4410_ = lean_ctor_get(v___x_4391_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4391_, 1);
v___x_4411_ = lean_box(0);
v___x_4412_ = l_Lean_Meta_Sym_letToHave___lam__0(v___y_4307_, v_zetaDeltaFVarIds_4327_, v___x_4411_);
lean_dec_ref(v___x_4412_);
v_a_4369_ = v_a_4410_;
goto v___jp_4368_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__3___boxed(lean_object* v___x_4420_, lean_object* v_e_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_){
_start:
{
uint8_t v___x_18590__boxed_4429_; lean_object* v_res_4430_; 
v___x_18590__boxed_4429_ = lean_unbox(v___x_4420_);
v_res_4430_ = l_Lean_Meta_Sym_letToHave___lam__3(v___x_18590__boxed_4429_, v_e_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_);
lean_dec(v___y_4427_);
lean_dec_ref(v___y_4426_);
lean_dec(v___y_4425_);
lean_dec_ref(v___y_4424_);
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
return v_res_4430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(lean_object* v_msg_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
lean_object* v_ref_4437_; lean_object* v___x_4438_; lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4447_; 
v_ref_4437_ = lean_ctor_get(v___y_4434_, 5);
v___x_4438_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(v_msg_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
v_a_4439_ = lean_ctor_get(v___x_4438_, 0);
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4447_ == 0)
{
v___x_4441_ = v___x_4438_;
v_isShared_4442_ = v_isSharedCheck_4447_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_dec(v___x_4438_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4447_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4443_; lean_object* v___x_4445_; 
lean_inc(v_ref_4437_);
v___x_4443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4443_, 0, v_ref_4437_);
lean_ctor_set(v___x_4443_, 1, v_a_4439_);
if (v_isShared_4442_ == 0)
{
lean_ctor_set_tag(v___x_4441_, 1);
lean_ctor_set(v___x_4441_, 0, v___x_4443_);
v___x_4445_ = v___x_4441_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v___x_4443_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg___boxed(lean_object* v_msg_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(v_msg_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(lean_object* v___y_4455_, uint8_t v_isExporting_4456_, lean_object* v___x_4457_, lean_object* v___y_4458_, lean_object* v___x_4459_, lean_object* v_a_x3f_4460_){
_start:
{
lean_object* v___x_4462_; lean_object* v_env_4463_; lean_object* v_nextMacroScope_4464_; lean_object* v_ngen_4465_; lean_object* v_auxDeclNGen_4466_; lean_object* v_traceState_4467_; lean_object* v_messages_4468_; lean_object* v_infoState_4469_; lean_object* v_snapshotTasks_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4495_; 
v___x_4462_ = lean_st_ref_take(v___y_4455_);
v_env_4463_ = lean_ctor_get(v___x_4462_, 0);
v_nextMacroScope_4464_ = lean_ctor_get(v___x_4462_, 1);
v_ngen_4465_ = lean_ctor_get(v___x_4462_, 2);
v_auxDeclNGen_4466_ = lean_ctor_get(v___x_4462_, 3);
v_traceState_4467_ = lean_ctor_get(v___x_4462_, 4);
v_messages_4468_ = lean_ctor_get(v___x_4462_, 6);
v_infoState_4469_ = lean_ctor_get(v___x_4462_, 7);
v_snapshotTasks_4470_ = lean_ctor_get(v___x_4462_, 8);
v_isSharedCheck_4495_ = !lean_is_exclusive(v___x_4462_);
if (v_isSharedCheck_4495_ == 0)
{
lean_object* v_unused_4496_; 
v_unused_4496_ = lean_ctor_get(v___x_4462_, 5);
lean_dec(v_unused_4496_);
v___x_4472_ = v___x_4462_;
v_isShared_4473_ = v_isSharedCheck_4495_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_snapshotTasks_4470_);
lean_inc(v_infoState_4469_);
lean_inc(v_messages_4468_);
lean_inc(v_traceState_4467_);
lean_inc(v_auxDeclNGen_4466_);
lean_inc(v_ngen_4465_);
lean_inc(v_nextMacroScope_4464_);
lean_inc(v_env_4463_);
lean_dec(v___x_4462_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4495_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4474_; lean_object* v___x_4476_; 
v___x_4474_ = l_Lean_Environment_setExporting(v_env_4463_, v_isExporting_4456_);
if (v_isShared_4473_ == 0)
{
lean_ctor_set(v___x_4472_, 5, v___x_4457_);
lean_ctor_set(v___x_4472_, 0, v___x_4474_);
v___x_4476_ = v___x_4472_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v___x_4474_);
lean_ctor_set(v_reuseFailAlloc_4494_, 1, v_nextMacroScope_4464_);
lean_ctor_set(v_reuseFailAlloc_4494_, 2, v_ngen_4465_);
lean_ctor_set(v_reuseFailAlloc_4494_, 3, v_auxDeclNGen_4466_);
lean_ctor_set(v_reuseFailAlloc_4494_, 4, v_traceState_4467_);
lean_ctor_set(v_reuseFailAlloc_4494_, 5, v___x_4457_);
lean_ctor_set(v_reuseFailAlloc_4494_, 6, v_messages_4468_);
lean_ctor_set(v_reuseFailAlloc_4494_, 7, v_infoState_4469_);
lean_ctor_set(v_reuseFailAlloc_4494_, 8, v_snapshotTasks_4470_);
v___x_4476_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v_mctx_4479_; lean_object* v_zetaDeltaFVarIds_4480_; lean_object* v_postponed_4481_; lean_object* v_diag_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4492_; 
v___x_4477_ = lean_st_ref_put(v___y_4455_, v___x_4476_);
v___x_4478_ = lean_st_ref_take(v___y_4458_);
v_mctx_4479_ = lean_ctor_get(v___x_4478_, 0);
v_zetaDeltaFVarIds_4480_ = lean_ctor_get(v___x_4478_, 2);
v_postponed_4481_ = lean_ctor_get(v___x_4478_, 3);
v_diag_4482_ = lean_ctor_get(v___x_4478_, 4);
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4478_);
if (v_isSharedCheck_4492_ == 0)
{
lean_object* v_unused_4493_; 
v_unused_4493_ = lean_ctor_get(v___x_4478_, 1);
lean_dec(v_unused_4493_);
v___x_4484_ = v___x_4478_;
v_isShared_4485_ = v_isSharedCheck_4492_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_diag_4482_);
lean_inc(v_postponed_4481_);
lean_inc(v_zetaDeltaFVarIds_4480_);
lean_inc(v_mctx_4479_);
lean_dec(v___x_4478_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4492_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4487_; 
if (v_isShared_4485_ == 0)
{
lean_ctor_set(v___x_4484_, 1, v___x_4459_);
v___x_4487_ = v___x_4484_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_mctx_4479_);
lean_ctor_set(v_reuseFailAlloc_4491_, 1, v___x_4459_);
lean_ctor_set(v_reuseFailAlloc_4491_, 2, v_zetaDeltaFVarIds_4480_);
lean_ctor_set(v_reuseFailAlloc_4491_, 3, v_postponed_4481_);
lean_ctor_set(v_reuseFailAlloc_4491_, 4, v_diag_4482_);
v___x_4487_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___x_4488_ = lean_st_ref_put(v___y_4458_, v___x_4487_);
v___x_4489_ = lean_box(0);
v___x_4490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4490_, 0, v___x_4489_);
return v___x_4490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_4497_, lean_object* v_isExporting_4498_, lean_object* v___x_4499_, lean_object* v___y_4500_, lean_object* v___x_4501_, lean_object* v_a_x3f_4502_, lean_object* v___y_4503_){
_start:
{
uint8_t v_isExporting_boxed_4504_; lean_object* v_res_4505_; 
v_isExporting_boxed_4504_ = lean_unbox(v_isExporting_4498_);
v_res_4505_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(v___y_4497_, v_isExporting_boxed_4504_, v___x_4499_, v___y_4500_, v___x_4501_, v_a_x3f_4502_);
lean_dec(v_a_x3f_4502_);
lean_dec(v___y_4500_);
lean_dec(v___y_4497_);
return v_res_4505_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4506_; 
v___x_4506_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4506_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4507_; lean_object* v___x_4508_; 
v___x_4507_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0);
v___x_4508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4508_, 0, v___x_4507_);
return v___x_4508_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4509_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1);
v___x_4510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4509_);
lean_ctor_set(v___x_4510_, 1, v___x_4509_);
return v___x_4510_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; 
v___x_4511_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1);
v___x_4512_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4511_);
lean_ctor_set(v___x_4512_, 1, v___x_4511_);
lean_ctor_set(v___x_4512_, 2, v___x_4511_);
lean_ctor_set(v___x_4512_, 3, v___x_4511_);
lean_ctor_set(v___x_4512_, 4, v___x_4511_);
lean_ctor_set(v___x_4512_, 5, v___x_4511_);
return v___x_4512_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(lean_object* v_x_4513_, uint8_t v_isExporting_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
lean_object* v___x_4522_; lean_object* v_env_4523_; uint8_t v_isExporting_4524_; lean_object* v___x_4590_; uint8_t v_isModule_4591_; 
v___x_4522_ = lean_st_ref_get(v___y_4520_);
v_env_4523_ = lean_ctor_get(v___x_4522_, 0);
lean_inc_ref(v_env_4523_);
lean_dec(v___x_4522_);
v_isExporting_4524_ = lean_ctor_get_uint8(v_env_4523_, sizeof(void*)*8);
v___x_4590_ = l_Lean_Environment_header(v_env_4523_);
lean_dec_ref(v_env_4523_);
v_isModule_4591_ = lean_ctor_get_uint8(v___x_4590_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4590_);
if (v_isModule_4591_ == 0)
{
lean_object* v___x_4592_; 
lean_inc(v___y_4520_);
lean_inc_ref(v___y_4519_);
lean_inc(v___y_4518_);
lean_inc_ref(v___y_4517_);
lean_inc(v___y_4516_);
lean_inc_ref(v___y_4515_);
v___x_4592_ = lean_apply_7(v_x_4513_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, lean_box(0));
return v___x_4592_;
}
else
{
if (v_isExporting_4524_ == 0)
{
if (v_isExporting_4514_ == 0)
{
lean_object* v___x_4593_; 
lean_inc(v___y_4520_);
lean_inc_ref(v___y_4519_);
lean_inc(v___y_4518_);
lean_inc_ref(v___y_4517_);
lean_inc(v___y_4516_);
lean_inc_ref(v___y_4515_);
v___x_4593_ = lean_apply_7(v_x_4513_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, lean_box(0));
return v___x_4593_;
}
else
{
goto v___jp_4525_;
}
}
else
{
if (v_isExporting_4514_ == 0)
{
goto v___jp_4525_;
}
else
{
lean_object* v___x_4594_; 
lean_inc(v___y_4520_);
lean_inc_ref(v___y_4519_);
lean_inc(v___y_4518_);
lean_inc_ref(v___y_4517_);
lean_inc(v___y_4516_);
lean_inc_ref(v___y_4515_);
v___x_4594_ = lean_apply_7(v_x_4513_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, lean_box(0));
return v___x_4594_;
}
}
}
v___jp_4525_:
{
lean_object* v___x_4526_; lean_object* v_env_4527_; lean_object* v_nextMacroScope_4528_; lean_object* v_ngen_4529_; lean_object* v_auxDeclNGen_4530_; lean_object* v_traceState_4531_; lean_object* v_messages_4532_; lean_object* v_infoState_4533_; lean_object* v_snapshotTasks_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4588_; 
v___x_4526_ = lean_st_ref_take(v___y_4520_);
v_env_4527_ = lean_ctor_get(v___x_4526_, 0);
v_nextMacroScope_4528_ = lean_ctor_get(v___x_4526_, 1);
v_ngen_4529_ = lean_ctor_get(v___x_4526_, 2);
v_auxDeclNGen_4530_ = lean_ctor_get(v___x_4526_, 3);
v_traceState_4531_ = lean_ctor_get(v___x_4526_, 4);
v_messages_4532_ = lean_ctor_get(v___x_4526_, 6);
v_infoState_4533_ = lean_ctor_get(v___x_4526_, 7);
v_snapshotTasks_4534_ = lean_ctor_get(v___x_4526_, 8);
v_isSharedCheck_4588_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4588_ == 0)
{
lean_object* v_unused_4589_; 
v_unused_4589_ = lean_ctor_get(v___x_4526_, 5);
lean_dec(v_unused_4589_);
v___x_4536_ = v___x_4526_;
v_isShared_4537_ = v_isSharedCheck_4588_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_snapshotTasks_4534_);
lean_inc(v_infoState_4533_);
lean_inc(v_messages_4532_);
lean_inc(v_traceState_4531_);
lean_inc(v_auxDeclNGen_4530_);
lean_inc(v_ngen_4529_);
lean_inc(v_nextMacroScope_4528_);
lean_inc(v_env_4527_);
lean_dec(v___x_4526_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4588_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4541_; 
v___x_4538_ = l_Lean_Environment_setExporting(v_env_4527_, v_isExporting_4514_);
v___x_4539_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2);
if (v_isShared_4537_ == 0)
{
lean_ctor_set(v___x_4536_, 5, v___x_4539_);
lean_ctor_set(v___x_4536_, 0, v___x_4538_);
v___x_4541_ = v___x_4536_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4587_; 
v_reuseFailAlloc_4587_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4587_, 0, v___x_4538_);
lean_ctor_set(v_reuseFailAlloc_4587_, 1, v_nextMacroScope_4528_);
lean_ctor_set(v_reuseFailAlloc_4587_, 2, v_ngen_4529_);
lean_ctor_set(v_reuseFailAlloc_4587_, 3, v_auxDeclNGen_4530_);
lean_ctor_set(v_reuseFailAlloc_4587_, 4, v_traceState_4531_);
lean_ctor_set(v_reuseFailAlloc_4587_, 5, v___x_4539_);
lean_ctor_set(v_reuseFailAlloc_4587_, 6, v_messages_4532_);
lean_ctor_set(v_reuseFailAlloc_4587_, 7, v_infoState_4533_);
lean_ctor_set(v_reuseFailAlloc_4587_, 8, v_snapshotTasks_4534_);
v___x_4541_ = v_reuseFailAlloc_4587_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v_mctx_4544_; lean_object* v_zetaDeltaFVarIds_4545_; lean_object* v_postponed_4546_; lean_object* v_diag_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4585_; 
v___x_4542_ = lean_st_ref_put(v___y_4520_, v___x_4541_);
v___x_4543_ = lean_st_ref_take(v___y_4518_);
v_mctx_4544_ = lean_ctor_get(v___x_4543_, 0);
v_zetaDeltaFVarIds_4545_ = lean_ctor_get(v___x_4543_, 2);
v_postponed_4546_ = lean_ctor_get(v___x_4543_, 3);
v_diag_4547_ = lean_ctor_get(v___x_4543_, 4);
v_isSharedCheck_4585_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4585_ == 0)
{
lean_object* v_unused_4586_; 
v_unused_4586_ = lean_ctor_get(v___x_4543_, 1);
lean_dec(v_unused_4586_);
v___x_4549_ = v___x_4543_;
v_isShared_4550_ = v_isSharedCheck_4585_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_diag_4547_);
lean_inc(v_postponed_4546_);
lean_inc(v_zetaDeltaFVarIds_4545_);
lean_inc(v_mctx_4544_);
lean_dec(v___x_4543_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4585_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
lean_object* v___x_4551_; lean_object* v___x_4553_; 
v___x_4551_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__3);
if (v_isShared_4550_ == 0)
{
lean_ctor_set(v___x_4549_, 1, v___x_4551_);
v___x_4553_ = v___x_4549_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v_mctx_4544_);
lean_ctor_set(v_reuseFailAlloc_4584_, 1, v___x_4551_);
lean_ctor_set(v_reuseFailAlloc_4584_, 2, v_zetaDeltaFVarIds_4545_);
lean_ctor_set(v_reuseFailAlloc_4584_, 3, v_postponed_4546_);
lean_ctor_set(v_reuseFailAlloc_4584_, 4, v_diag_4547_);
v___x_4553_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
lean_object* v___x_4554_; lean_object* v_r_4555_; 
v___x_4554_ = lean_st_ref_put(v___y_4518_, v___x_4553_);
lean_inc(v___y_4520_);
lean_inc_ref(v___y_4519_);
lean_inc(v___y_4518_);
lean_inc_ref(v___y_4517_);
lean_inc(v___y_4516_);
lean_inc_ref(v___y_4515_);
v_r_4555_ = lean_apply_7(v_x_4513_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, lean_box(0));
if (lean_obj_tag(v_r_4555_) == 0)
{
lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4572_; 
v_a_4556_ = lean_ctor_get(v_r_4555_, 0);
v_isSharedCheck_4572_ = !lean_is_exclusive(v_r_4555_);
if (v_isSharedCheck_4572_ == 0)
{
v___x_4558_ = v_r_4555_;
v_isShared_4559_ = v_isSharedCheck_4572_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_dec(v_r_4555_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4572_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4561_; 
lean_inc(v_a_4556_);
if (v_isShared_4559_ == 0)
{
lean_ctor_set_tag(v___x_4558_, 1);
v___x_4561_ = v___x_4558_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v_a_4556_);
v___x_4561_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
lean_object* v___x_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4569_; 
v___x_4562_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(v___y_4520_, v_isExporting_4524_, v___x_4539_, v___y_4518_, v___x_4551_, v___x_4561_);
lean_dec_ref(v___x_4561_);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4569_ == 0)
{
lean_object* v_unused_4570_; 
v_unused_4570_ = lean_ctor_get(v___x_4562_, 0);
lean_dec(v_unused_4570_);
v___x_4564_ = v___x_4562_;
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
else
{
lean_dec(v___x_4562_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4567_; 
if (v_isShared_4565_ == 0)
{
lean_ctor_set(v___x_4564_, 0, v_a_4556_);
v___x_4567_ = v___x_4564_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_a_4556_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
}
}
}
else
{
lean_object* v_a_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4582_; 
v_a_4573_ = lean_ctor_get(v_r_4555_, 0);
lean_inc(v_a_4573_);
lean_dec_ref_known(v_r_4555_, 1);
v___x_4574_ = lean_box(0);
v___x_4575_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(v___y_4520_, v_isExporting_4524_, v___x_4539_, v___y_4518_, v___x_4551_, v___x_4574_);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4575_);
if (v_isSharedCheck_4582_ == 0)
{
lean_object* v_unused_4583_; 
v_unused_4583_ = lean_ctor_get(v___x_4575_, 0);
lean_dec(v_unused_4583_);
v___x_4577_ = v___x_4575_;
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
else
{
lean_dec(v___x_4575_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4580_; 
if (v_isShared_4578_ == 0)
{
lean_ctor_set_tag(v___x_4577_, 1);
lean_ctor_set(v___x_4577_, 0, v_a_4573_);
v___x_4580_ = v___x_4577_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_a_4573_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
return v___x_4580_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___boxed(lean_object* v_x_4595_, lean_object* v_isExporting_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_){
_start:
{
uint8_t v_isExporting_boxed_4604_; lean_object* v_res_4605_; 
v_isExporting_boxed_4604_ = lean_unbox(v_isExporting_4596_);
v_res_4605_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(v_x_4595_, v_isExporting_boxed_4604_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_);
lean_dec(v___y_4602_);
lean_dec_ref(v___y_4601_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
lean_dec(v___y_4598_);
lean_dec_ref(v___y_4597_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(lean_object* v_x_4606_, uint8_t v_when_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_){
_start:
{
if (v_when_4607_ == 0)
{
lean_object* v___x_4615_; 
lean_inc(v___y_4613_);
lean_inc_ref(v___y_4612_);
lean_inc(v___y_4611_);
lean_inc_ref(v___y_4610_);
lean_inc(v___y_4609_);
lean_inc_ref(v___y_4608_);
v___x_4615_ = lean_apply_7(v_x_4606_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_, lean_box(0));
return v___x_4615_;
}
else
{
uint8_t v___x_4616_; lean_object* v___x_4617_; 
v___x_4616_ = 0;
v___x_4617_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(v_x_4606_, v___x_4616_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_);
return v___x_4617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg___boxed(lean_object* v_x_4618_, lean_object* v_when_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_){
_start:
{
uint8_t v_when_boxed_4627_; lean_object* v_res_4628_; 
v_when_boxed_4627_ = lean_unbox(v_when_4619_);
v_res_4628_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(v_x_4618_, v_when_boxed_4627_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_);
lean_dec(v___y_4625_);
lean_dec_ref(v___y_4624_);
lean_dec(v___y_4623_);
lean_dec_ref(v___y_4622_);
lean_dec(v___y_4621_);
lean_dec_ref(v___y_4620_);
return v_res_4628_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___closed__1(void){
_start:
{
lean_object* v___x_4630_; lean_object* v___x_4631_; 
v___x_4630_ = ((lean_object*)(l_Lean_Meta_Sym_letToHave___closed__0));
v___x_4631_ = l_Lean_stringToMessageData(v___x_4630_);
return v___x_4631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave(lean_object* v_e_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_){
_start:
{
lean_object* v___y_4641_; lean_object* v___y_4642_; lean_object* v___y_4643_; lean_object* v___y_4644_; lean_object* v___y_4645_; lean_object* v___y_4646_; uint8_t v___x_4655_; 
v___x_4655_ = l_Lean_Expr_hasLooseBVars(v_e_4632_);
if (v___x_4655_ == 0)
{
v___y_4641_ = v_a_4633_;
v___y_4642_ = v_a_4634_;
v___y_4643_ = v_a_4635_;
v___y_4644_ = v_a_4636_;
v___y_4645_ = v_a_4637_;
v___y_4646_ = v_a_4638_;
goto v___jp_4640_;
}
else
{
lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v_a_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4665_; 
lean_dec_ref(v_e_4632_);
v___x_4656_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___closed__1, &l_Lean_Meta_Sym_letToHave___closed__1_once, _init_l_Lean_Meta_Sym_letToHave___closed__1);
v___x_4657_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(v___x_4656_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_);
v_a_4658_ = lean_ctor_get(v___x_4657_, 0);
v_isSharedCheck_4665_ = !lean_is_exclusive(v___x_4657_);
if (v_isSharedCheck_4665_ == 0)
{
v___x_4660_ = v___x_4657_;
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_a_4658_);
lean_dec(v___x_4657_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v___x_4663_; 
if (v_isShared_4661_ == 0)
{
v___x_4663_ = v___x_4660_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v_a_4658_);
v___x_4663_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
return v___x_4663_;
}
}
}
v___jp_4640_:
{
uint8_t v___x_4647_; lean_object* v___x_4648_; lean_object* v___f_4649_; uint8_t v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; uint8_t v___x_4653_; lean_object* v___x_4654_; 
v___x_4647_ = 0;
v___x_4648_ = lean_box(v___x_4647_);
v___f_4649_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_letToHave___lam__3___boxed), 9, 2);
lean_closure_set(v___f_4649_, 0, v___x_4648_);
lean_closure_set(v___f_4649_, 1, v_e_4632_);
v___x_4650_ = 0;
v___x_4651_ = lean_box(v___x_4650_);
v___x_4652_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___boxed), 10, 3);
lean_closure_set(v___x_4652_, 0, lean_box(0));
lean_closure_set(v___x_4652_, 1, v___f_4649_);
lean_closure_set(v___x_4652_, 2, v___x_4651_);
v___x_4653_ = 1;
v___x_4654_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(v___x_4652_, v___x_4653_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_);
return v___x_4654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___boxed(lean_object* v_e_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_){
_start:
{
lean_object* v_res_4674_; 
v_res_4674_ = l_Lean_Meta_Sym_letToHave(v_e_4666_, v_a_4667_, v_a_4668_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_);
lean_dec(v_a_4672_);
lean_dec_ref(v_a_4671_);
lean_dec(v_a_4670_);
lean_dec_ref(v_a_4669_);
lean_dec(v_a_4668_);
lean_dec_ref(v_a_4667_);
return v_res_4674_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2(lean_object* v_00_u03b1_4675_, lean_object* v_x_4676_, uint8_t v_isExporting_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_){
_start:
{
lean_object* v___x_4685_; 
v___x_4685_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(v_x_4676_, v_isExporting_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_);
return v___x_4685_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___boxed(lean_object* v_00_u03b1_4686_, lean_object* v_x_4687_, lean_object* v_isExporting_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_){
_start:
{
uint8_t v_isExporting_boxed_4696_; lean_object* v_res_4697_; 
v_isExporting_boxed_4696_ = lean_unbox(v_isExporting_4688_);
v_res_4697_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2(v_00_u03b1_4686_, v_x_4687_, v_isExporting_boxed_4696_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
lean_dec(v___y_4694_);
lean_dec_ref(v___y_4693_);
lean_dec(v___y_4692_);
lean_dec_ref(v___y_4691_);
lean_dec(v___y_4690_);
lean_dec_ref(v___y_4689_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2(lean_object* v_00_u03b1_4698_, lean_object* v_x_4699_, uint8_t v_when_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_){
_start:
{
lean_object* v___x_4708_; 
v___x_4708_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(v_x_4699_, v_when_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_);
return v___x_4708_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___boxed(lean_object* v_00_u03b1_4709_, lean_object* v_x_4710_, lean_object* v_when_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_){
_start:
{
uint8_t v_when_boxed_4719_; lean_object* v_res_4720_; 
v_when_boxed_4719_ = lean_unbox(v_when_4711_);
v_res_4720_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2(v_00_u03b1_4709_, v_x_4710_, v_when_boxed_4719_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_);
lean_dec(v___y_4717_);
lean_dec_ref(v___y_4716_);
lean_dec(v___y_4715_);
lean_dec_ref(v___y_4714_);
lean_dec(v___y_4713_);
lean_dec_ref(v___y_4712_);
return v_res_4720_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3(lean_object* v_00_u03b1_4721_, lean_object* v_msg_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_){
_start:
{
lean_object* v___x_4730_; 
v___x_4730_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(v_msg_4722_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
return v___x_4730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___boxed(lean_object* v_00_u03b1_4731_, lean_object* v_msg_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_){
_start:
{
lean_object* v_res_4740_; 
v_res_4740_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3(v_00_u03b1_4731_, v_msg_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
return v_res_4740_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_LetToHave(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_LetToHave(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_LetToHave(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LetToHave(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_LetToHave(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_LetToHave(builtin);
}
#ifdef __cplusplus
}
#endif
