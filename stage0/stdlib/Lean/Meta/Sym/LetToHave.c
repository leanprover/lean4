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
lean_object* l_EStateM_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVar_x21(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg();
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getZetaDeltaFVarIds___redArg(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Meta.Sym.LetToHave.0.Lean.Meta.Sym.LetToHave.visitCore"};
static const lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_letToHave___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_letToHave___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_letToHave___lam__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_letToHave___lam__5___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_letToHave___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_letToHave___lam__5___closed__1;
static lean_once_cell_t l_Lean_Meta_Sym_letToHave___lam__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_letToHave___lam__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_letToHave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_letToHave___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_letToHave___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_letToHave___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_letToHave___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "`Sym.letToHave` internal error, input term has loose bound variables"};
static const lean_object* l_Lean_Meta_Sym_letToHave___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_letToHave___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_letToHave___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_letToHave___closed__2;
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
lean_object* v___x_14_; lean_object* v___x_16_; 
v___x_14_ = lean_box(0);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 2, v_subst_4_);
lean_ctor_set(v___x_12_, 1, v_types_3_);
lean_ctor_set(v___x_12_, 0, v_visited_2_);
v___x_16_ = v___x_12_;
goto v_reusejp_15_;
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
v___x_16_ = v_reuseFailAlloc_19_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_st_ref_put(v_a_1_, v___x_16_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_14_);
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
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v_nbuckets_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_215_ = lean_array_get_size(v_data_214_);
v___x_216_ = lean_unsigned_to_nat(2u);
v_nbuckets_217_ = lean_nat_mul(v___x_215_, v___x_216_);
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_box(0);
v___x_220_ = lean_mk_array(v_nbuckets_217_, v___x_219_);
v___x_221_ = lean_array_propagate_mark(v_data_214_, v___x_220_);
v___x_222_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4___redArg(v___x_218_, v_data_214_, v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__4___redArg(lean_object* v_a_223_, lean_object* v_b_224_, lean_object* v_x_225_){
_start:
{
if (lean_obj_tag(v_x_225_) == 0)
{
lean_dec(v_b_224_);
lean_dec_ref(v_a_223_);
return v_x_225_;
}
else
{
lean_object* v_key_226_; lean_object* v_value_227_; lean_object* v_tail_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_242_; 
v_key_226_ = lean_ctor_get(v_x_225_, 0);
v_value_227_ = lean_ctor_get(v_x_225_, 1);
v_tail_228_ = lean_ctor_get(v_x_225_, 2);
v_isSharedCheck_242_ = !lean_is_exclusive(v_x_225_);
if (v_isSharedCheck_242_ == 0)
{
v___x_230_ = v_x_225_;
v_isShared_231_ = v_isSharedCheck_242_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_tail_228_);
lean_inc(v_value_227_);
lean_inc(v_key_226_);
lean_dec(v_x_225_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_242_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
size_t v___x_232_; size_t v___x_233_; uint8_t v___x_234_; 
v___x_232_ = lean_ptr_addr(v_key_226_);
v___x_233_ = lean_ptr_addr(v_a_223_);
v___x_234_ = lean_usize_dec_eq(v___x_232_, v___x_233_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_235_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__4___redArg(v_a_223_, v_b_224_, v_tail_228_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 2, v___x_235_);
v___x_237_ = v___x_230_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_key_226_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_value_227_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
else
{
lean_object* v___x_240_; 
lean_dec(v_value_227_);
lean_dec(v_key_226_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v_b_224_);
lean_ctor_set(v___x_230_, 0, v_a_223_);
v___x_240_ = v___x_230_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_223_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_b_224_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_tail_228_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___redArg(lean_object* v_a_243_, lean_object* v_x_244_){
_start:
{
if (lean_obj_tag(v_x_244_) == 0)
{
uint8_t v___x_245_; 
v___x_245_ = 0;
return v___x_245_;
}
else
{
lean_object* v_key_246_; lean_object* v_tail_247_; size_t v___x_248_; size_t v___x_249_; uint8_t v___x_250_; 
v_key_246_ = lean_ctor_get(v_x_244_, 0);
v_tail_247_ = lean_ctor_get(v_x_244_, 2);
v___x_248_ = lean_ptr_addr(v_key_246_);
v___x_249_ = lean_ptr_addr(v_a_243_);
v___x_250_ = lean_usize_dec_eq(v___x_248_, v___x_249_);
if (v___x_250_ == 0)
{
v_x_244_ = v_tail_247_;
goto _start;
}
else
{
return v___x_250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___redArg___boxed(lean_object* v_a_252_, lean_object* v_x_253_){
_start:
{
uint8_t v_res_254_; lean_object* v_r_255_; 
v_res_254_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___redArg(v_a_252_, v_x_253_);
lean_dec(v_x_253_);
lean_dec_ref(v_a_252_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(lean_object* v_m_256_, lean_object* v_a_257_, lean_object* v_b_258_){
_start:
{
lean_object* v_size_259_; lean_object* v_buckets_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_306_; 
v_size_259_ = lean_ctor_get(v_m_256_, 0);
v_buckets_260_ = lean_ctor_get(v_m_256_, 1);
v_isSharedCheck_306_ = !lean_is_exclusive(v_m_256_);
if (v_isSharedCheck_306_ == 0)
{
v___x_262_ = v_m_256_;
v_isShared_263_ = v_isSharedCheck_306_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_buckets_260_);
lean_inc(v_size_259_);
lean_dec(v_m_256_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_306_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; size_t v___x_265_; size_t v___x_266_; size_t v___x_267_; uint64_t v___x_268_; uint64_t v___x_269_; uint64_t v___x_270_; uint64_t v_fold_271_; uint64_t v___x_272_; uint64_t v___x_273_; uint64_t v___x_274_; size_t v___x_275_; size_t v___x_276_; size_t v___x_277_; size_t v___x_278_; size_t v___x_279_; lean_object* v_bkt_280_; uint8_t v___x_281_; 
v___x_264_ = lean_array_get_size(v_buckets_260_);
v___x_265_ = lean_ptr_addr(v_a_257_);
v___x_266_ = ((size_t)3ULL);
v___x_267_ = lean_usize_shift_right(v___x_265_, v___x_266_);
v___x_268_ = lean_usize_to_uint64(v___x_267_);
v___x_269_ = 32ULL;
v___x_270_ = lean_uint64_shift_right(v___x_268_, v___x_269_);
v_fold_271_ = lean_uint64_xor(v___x_268_, v___x_270_);
v___x_272_ = 16ULL;
v___x_273_ = lean_uint64_shift_right(v_fold_271_, v___x_272_);
v___x_274_ = lean_uint64_xor(v_fold_271_, v___x_273_);
v___x_275_ = lean_uint64_to_usize(v___x_274_);
v___x_276_ = lean_usize_of_nat(v___x_264_);
v___x_277_ = ((size_t)1ULL);
v___x_278_ = lean_usize_sub(v___x_276_, v___x_277_);
v___x_279_ = lean_usize_land(v___x_275_, v___x_278_);
v_bkt_280_ = lean_array_uget_borrowed(v_buckets_260_, v___x_279_);
v___x_281_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___redArg(v_a_257_, v_bkt_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v_size_x27_283_; lean_object* v___x_284_; lean_object* v_buckets_x27_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_282_ = lean_unsigned_to_nat(1u);
v_size_x27_283_ = lean_nat_add(v_size_259_, v___x_282_);
lean_dec(v_size_259_);
lean_inc(v_bkt_280_);
v___x_284_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_284_, 0, v_a_257_);
lean_ctor_set(v___x_284_, 1, v_b_258_);
lean_ctor_set(v___x_284_, 2, v_bkt_280_);
v_buckets_x27_285_ = lean_array_uset(v_buckets_260_, v___x_279_, v___x_284_);
v___x_286_ = lean_unsigned_to_nat(4u);
v___x_287_ = lean_nat_mul(v_size_x27_283_, v___x_286_);
v___x_288_ = lean_unsigned_to_nat(3u);
v___x_289_ = lean_nat_div(v___x_287_, v___x_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_array_get_size(v_buckets_x27_285_);
v___x_291_ = lean_nat_dec_le(v___x_289_, v___x_290_);
lean_dec(v___x_289_);
if (v___x_291_ == 0)
{
lean_object* v_val_292_; lean_object* v___x_294_; 
v_val_292_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3___redArg(v_buckets_x27_285_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v_val_292_);
lean_ctor_set(v___x_262_, 0, v_size_x27_283_);
v___x_294_ = v___x_262_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_size_x27_283_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_val_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
else
{
lean_object* v___x_297_; 
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v_buckets_x27_285_);
lean_ctor_set(v___x_262_, 0, v_size_x27_283_);
v___x_297_ = v___x_262_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_size_x27_283_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_buckets_x27_285_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
else
{
lean_object* v___x_299_; lean_object* v_buckets_x27_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
lean_inc(v_bkt_280_);
v___x_299_ = lean_box(0);
v_buckets_x27_300_ = lean_array_uset(v_buckets_260_, v___x_279_, v___x_299_);
v___x_301_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__4___redArg(v_a_257_, v_b_258_, v_bkt_280_);
v___x_302_ = lean_array_uset(v_buckets_x27_300_, v___x_279_, v___x_301_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___x_302_);
v___x_304_ = v___x_262_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_size_259_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___redArg(lean_object* v_a_307_, lean_object* v_x_308_){
_start:
{
if (lean_obj_tag(v_x_308_) == 0)
{
lean_object* v___x_309_; 
v___x_309_ = lean_box(0);
return v___x_309_;
}
else
{
lean_object* v_key_310_; lean_object* v_value_311_; lean_object* v_tail_312_; size_t v___x_313_; size_t v___x_314_; uint8_t v___x_315_; 
v_key_310_ = lean_ctor_get(v_x_308_, 0);
v_value_311_ = lean_ctor_get(v_x_308_, 1);
v_tail_312_ = lean_ctor_get(v_x_308_, 2);
v___x_313_ = lean_ptr_addr(v_key_310_);
v___x_314_ = lean_ptr_addr(v_a_307_);
v___x_315_ = lean_usize_dec_eq(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
v_x_308_ = v_tail_312_;
goto _start;
}
else
{
lean_object* v___x_317_; 
lean_inc(v_value_311_);
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v_value_311_);
return v___x_317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___redArg___boxed(lean_object* v_a_318_, lean_object* v_x_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___redArg(v_a_318_, v_x_319_);
lean_dec(v_x_319_);
lean_dec_ref(v_a_318_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(lean_object* v_m_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_buckets_323_; lean_object* v___x_324_; size_t v___x_325_; size_t v___x_326_; size_t v___x_327_; uint64_t v___x_328_; uint64_t v___x_329_; uint64_t v___x_330_; uint64_t v_fold_331_; uint64_t v___x_332_; uint64_t v___x_333_; uint64_t v___x_334_; size_t v___x_335_; size_t v___x_336_; size_t v___x_337_; size_t v___x_338_; size_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_buckets_323_ = lean_ctor_get(v_m_321_, 1);
v___x_324_ = lean_array_get_size(v_buckets_323_);
v___x_325_ = lean_ptr_addr(v_a_322_);
v___x_326_ = ((size_t)3ULL);
v___x_327_ = lean_usize_shift_right(v___x_325_, v___x_326_);
v___x_328_ = lean_usize_to_uint64(v___x_327_);
v___x_329_ = 32ULL;
v___x_330_ = lean_uint64_shift_right(v___x_328_, v___x_329_);
v_fold_331_ = lean_uint64_xor(v___x_328_, v___x_330_);
v___x_332_ = 16ULL;
v___x_333_ = lean_uint64_shift_right(v_fold_331_, v___x_332_);
v___x_334_ = lean_uint64_xor(v_fold_331_, v___x_333_);
v___x_335_ = lean_uint64_to_usize(v___x_334_);
v___x_336_ = lean_usize_of_nat(v___x_324_);
v___x_337_ = ((size_t)1ULL);
v___x_338_ = lean_usize_sub(v___x_336_, v___x_337_);
v___x_339_ = lean_usize_land(v___x_335_, v___x_338_);
v___x_340_ = lean_array_uget_borrowed(v_buckets_323_, v___x_339_);
v___x_341_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___redArg(v_a_322_, v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg___boxed(lean_object* v_m_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_m_342_, v_a_343_);
lean_dec_ref(v_a_343_);
lean_dec_ref(v_m_342_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(lean_object* v_e_345_, lean_object* v_k_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v___x_356_; lean_object* v_hasDepLetCache_357_; lean_object* v___x_358_; 
v___x_356_ = lean_st_ref_get(v_a_348_);
v_hasDepLetCache_357_ = lean_ctor_get(v___x_356_, 4);
lean_inc_ref(v_hasDepLetCache_357_);
lean_dec(v___x_356_);
v___x_358_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_hasDepLetCache_357_, v_e_345_);
lean_dec_ref(v_hasDepLetCache_357_);
if (lean_obj_tag(v___x_358_) == 1)
{
lean_object* v_val_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec_ref(v_k_346_);
lean_dec_ref(v_e_345_);
v_val_359_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_358_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_val_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
lean_ctor_set_tag(v___x_361_, 0);
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_val_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
else
{
lean_object* v___x_367_; 
lean_dec(v___x_358_);
lean_inc(v_a_354_);
lean_inc_ref(v_a_353_);
lean_inc(v_a_352_);
lean_inc_ref(v_a_351_);
lean_inc(v_a_350_);
lean_inc_ref(v_a_349_);
lean_inc(v_a_348_);
lean_inc_ref(v_a_347_);
v___x_367_ = lean_apply_9(v_k_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, lean_box(0));
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_391_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_391_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_391_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_391_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v_visited_373_; lean_object* v_types_374_; lean_object* v_subst_375_; lean_object* v_visitedClosed_376_; lean_object* v_hasDepLetCache_377_; lean_object* v_numConverted_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_390_; 
v___x_372_ = lean_st_ref_take(v_a_348_);
v_visited_373_ = lean_ctor_get(v___x_372_, 0);
v_types_374_ = lean_ctor_get(v___x_372_, 1);
v_subst_375_ = lean_ctor_get(v___x_372_, 2);
v_visitedClosed_376_ = lean_ctor_get(v___x_372_, 3);
v_hasDepLetCache_377_ = lean_ctor_get(v___x_372_, 4);
v_numConverted_378_ = lean_ctor_get(v___x_372_, 5);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_390_ == 0)
{
v___x_380_ = v___x_372_;
v_isShared_381_ = v_isSharedCheck_390_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_numConverted_378_);
lean_inc(v_hasDepLetCache_377_);
lean_inc(v_visitedClosed_376_);
lean_inc(v_subst_375_);
lean_inc(v_types_374_);
lean_inc(v_visited_373_);
lean_dec(v___x_372_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_390_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; lean_object* v___x_384_; 
lean_inc(v_a_368_);
v___x_382_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_hasDepLetCache_377_, v_e_345_, v_a_368_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 4, v___x_382_);
v___x_384_ = v___x_380_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_visited_373_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_types_374_);
lean_ctor_set(v_reuseFailAlloc_389_, 2, v_subst_375_);
lean_ctor_set(v_reuseFailAlloc_389_, 3, v_visitedClosed_376_);
lean_ctor_set(v_reuseFailAlloc_389_, 4, v___x_382_);
lean_ctor_set(v_reuseFailAlloc_389_, 5, v_numConverted_378_);
v___x_384_ = v_reuseFailAlloc_389_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_385_ = lean_st_ref_put(v_a_348_, v___x_384_);
if (v_isShared_371_ == 0)
{
v___x_387_ = v___x_370_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_368_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_345_);
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached___boxed(lean_object* v_e_392_, lean_object* v_k_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(v_e_392_, v_k_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0(lean_object* v_00_u03b2_404_, lean_object* v_m_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_m_405_, v_a_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___boxed(lean_object* v_00_u03b2_408_, lean_object* v_m_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0(v_00_u03b2_408_, v_m_409_, v_a_410_);
lean_dec_ref(v_a_410_);
lean_dec_ref(v_m_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1(lean_object* v_00_u03b2_412_, lean_object* v_m_413_, lean_object* v_a_414_, lean_object* v_b_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_m_413_, v_a_414_, v_b_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0(lean_object* v_00_u03b2_417_, lean_object* v_a_418_, lean_object* v_x_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___redArg(v_a_418_, v_x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_421_, lean_object* v_a_422_, lean_object* v_x_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0(v_00_u03b2_421_, v_a_422_, v_x_423_);
lean_dec(v_x_423_);
lean_dec_ref(v_a_422_);
return v_res_424_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2(lean_object* v_00_u03b2_425_, lean_object* v_a_426_, lean_object* v_x_427_){
_start:
{
uint8_t v___x_428_; 
v___x_428_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___redArg(v_a_426_, v_x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___boxed(lean_object* v_00_u03b2_429_, lean_object* v_a_430_, lean_object* v_x_431_){
_start:
{
uint8_t v_res_432_; lean_object* v_r_433_; 
v_res_432_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2(v_00_u03b2_429_, v_a_430_, v_x_431_);
lean_dec(v_x_431_);
lean_dec_ref(v_a_430_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3(lean_object* v_00_u03b2_434_, lean_object* v_data_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3___redArg(v_data_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__4(lean_object* v_00_u03b2_437_, lean_object* v_a_438_, lean_object* v_b_439_, lean_object* v_x_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__4___redArg(v_a_438_, v_b_439_, v_x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_442_, lean_object* v_i_443_, lean_object* v_source_444_, lean_object* v_target_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4___redArg(v_i_443_, v_source_444_, v_target_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_447_, lean_object* v_x_448_, lean_object* v_x_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4_spec__5___redArg(v_x_448_, v_x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__0___boxed(lean_object* v_t_451_, lean_object* v_b_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__0(v_t_451_, v_b_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__1(lean_object* v_type_463_, lean_object* v_value_464_, lean_object* v_body_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_type_463_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; uint8_t v___x_477_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
v___x_477_ = lean_unbox(v_a_476_);
lean_dec(v_a_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; 
lean_dec_ref_known(v___x_475_, 1);
v___x_478_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_value_464_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; uint8_t v___x_480_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
v___x_480_ = lean_unbox(v_a_479_);
lean_dec(v_a_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; 
lean_dec_ref_known(v___x_478_, 1);
v___x_481_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_body_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
return v___x_481_;
}
else
{
lean_dec_ref(v_body_465_);
return v___x_478_;
}
}
else
{
lean_dec_ref(v_body_465_);
return v___x_478_;
}
}
else
{
lean_dec_ref(v_body_465_);
lean_dec_ref(v_value_464_);
return v___x_475_;
}
}
else
{
lean_dec_ref(v_body_465_);
lean_dec_ref(v_value_464_);
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__1___boxed(lean_object* v_type_482_, lean_object* v_value_483_, lean_object* v_body_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__1(v_type_482_, v_value_483_, v_body_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__2(lean_object* v_fn_495_, lean_object* v_arg_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_fn_495_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; uint8_t v___x_508_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
v___x_508_ = lean_unbox(v_a_507_);
lean_dec(v_a_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
lean_dec_ref_known(v___x_506_, 1);
v___x_509_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_arg_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
return v___x_509_;
}
else
{
lean_dec_ref(v_arg_496_);
return v___x_506_;
}
}
else
{
lean_dec_ref(v_arg_496_);
return v___x_506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__2___boxed(lean_object* v_fn_510_, lean_object* v_arg_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__2(v_fn_510_, v_arg_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___boxed(lean_object* v_e_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_e_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(lean_object* v_e_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_t_544_; lean_object* v_b_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; 
switch(lean_obj_tag(v_e_533_))
{
case 8:
{
uint8_t v_nondep_556_; 
v_nondep_556_ = lean_ctor_get_uint8(v_e_533_, sizeof(void*)*4 + 8);
if (v_nondep_556_ == 0)
{
uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec_ref_known(v_e_533_, 4);
v___x_557_ = 1;
v___x_558_ = lean_box(v___x_557_);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
else
{
lean_object* v_type_560_; lean_object* v_value_561_; lean_object* v_body_562_; lean_object* v___f_563_; lean_object* v___x_564_; 
v_type_560_ = lean_ctor_get(v_e_533_, 1);
v_value_561_ = lean_ctor_get(v_e_533_, 2);
v_body_562_ = lean_ctor_get(v_e_533_, 3);
lean_inc_ref(v_body_562_);
lean_inc_ref(v_value_561_);
lean_inc_ref(v_type_560_);
v___f_563_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__1___boxed), 12, 3);
lean_closure_set(v___f_563_, 0, v_type_560_);
lean_closure_set(v___f_563_, 1, v_value_561_);
lean_closure_set(v___f_563_, 2, v_body_562_);
v___x_564_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(v_e_533_, v___f_563_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
return v___x_564_;
}
}
case 5:
{
lean_object* v_fn_565_; lean_object* v_arg_566_; lean_object* v___f_567_; lean_object* v___x_568_; 
v_fn_565_ = lean_ctor_get(v_e_533_, 0);
v_arg_566_ = lean_ctor_get(v_e_533_, 1);
lean_inc_ref(v_arg_566_);
lean_inc_ref(v_fn_565_);
v___f_567_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__2___boxed), 11, 2);
lean_closure_set(v___f_567_, 0, v_fn_565_);
lean_closure_set(v___f_567_, 1, v_arg_566_);
v___x_568_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(v_e_533_, v___f_567_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
return v___x_568_;
}
case 6:
{
lean_object* v_binderType_569_; lean_object* v_body_570_; 
v_binderType_569_ = lean_ctor_get(v_e_533_, 1);
v_body_570_ = lean_ctor_get(v_e_533_, 2);
lean_inc_ref(v_body_570_);
lean_inc_ref(v_binderType_569_);
v_t_544_ = v_binderType_569_;
v_b_545_ = v_body_570_;
v___y_546_ = v_a_534_;
v___y_547_ = v_a_535_;
v___y_548_ = v_a_536_;
v___y_549_ = v_a_537_;
v___y_550_ = v_a_538_;
v___y_551_ = v_a_539_;
v___y_552_ = v_a_540_;
v___y_553_ = v_a_541_;
goto v___jp_543_;
}
case 7:
{
lean_object* v_binderType_571_; lean_object* v_body_572_; 
v_binderType_571_ = lean_ctor_get(v_e_533_, 1);
v_body_572_ = lean_ctor_get(v_e_533_, 2);
lean_inc_ref(v_body_572_);
lean_inc_ref(v_binderType_571_);
v_t_544_ = v_binderType_571_;
v_b_545_ = v_body_572_;
v___y_546_ = v_a_534_;
v___y_547_ = v_a_535_;
v___y_548_ = v_a_536_;
v___y_549_ = v_a_537_;
v___y_550_ = v_a_538_;
v___y_551_ = v_a_539_;
v___y_552_ = v_a_540_;
v___y_553_ = v_a_541_;
goto v___jp_543_;
}
case 10:
{
lean_object* v_expr_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_expr_573_ = lean_ctor_get(v_e_533_, 1);
lean_inc_ref(v_expr_573_);
v___x_574_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___boxed), 10, 1);
lean_closure_set(v___x_574_, 0, v_expr_573_);
v___x_575_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(v_e_533_, v___x_574_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
return v___x_575_;
}
case 11:
{
lean_object* v_struct_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v_struct_576_ = lean_ctor_get(v_e_533_, 2);
lean_inc_ref(v_struct_576_);
v___x_577_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___boxed), 10, 1);
lean_closure_set(v___x_577_, 0, v_struct_576_);
v___x_578_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(v_e_533_, v___x_577_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
return v___x_578_;
}
default: 
{
uint8_t v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec_ref(v_e_533_);
v___x_579_ = 0;
v___x_580_ = lean_box(v___x_579_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
v___jp_543_:
{
lean_object* v___f_554_; lean_object* v___x_555_; 
v___f_554_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__0___boxed), 11, 2);
lean_closure_set(v___f_554_, 0, v_t_544_);
lean_closure_set(v___f_554_, 1, v_b_545_);
v___x_555_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(v_e_533_, v___f_554_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
return v___x_555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__0(lean_object* v_t_582_, lean_object* v_b_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_t_582_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; uint8_t v___x_595_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
v___x_595_ = lean_unbox(v_a_594_);
lean_dec(v_a_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
lean_dec_ref_known(v___x_593_, 1);
v___x_596_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_b_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
return v___x_596_;
}
else
{
lean_dec_ref(v_b_583_);
return v___x_593_;
}
}
else
{
lean_dec_ref(v_b_583_);
return v___x_593_;
}
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___closed__0(void){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1(lean_object* v_msg_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v___x_606_; lean_object* v___x_10876__overap_607_; lean_object* v___x_608_; 
v___x_606_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___closed__0);
v___x_10876__overap_607_ = lean_panic_fn_borrowed(v___x_606_, v_msg_598_);
lean_inc(v___y_604_);
lean_inc_ref(v___y_603_);
lean_inc(v___y_602_);
lean_inc_ref(v___y_601_);
lean_inc(v___y_600_);
lean_inc_ref(v___y_599_);
v___x_608_ = lean_apply_7(v___x_10876__overap_607_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, lean_box(0));
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___boxed(lean_object* v_msg_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1(v_msg_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1(lean_object* v_f_618_, lean_object* v_a_619_, lean_object* v___y_620_, uint8_t v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___y_625_; lean_object* v___y_626_; 
if (v___y_621_ == 0)
{
v___y_625_ = v___y_620_;
v___y_626_ = v___y_623_;
goto v___jp_624_;
}
else
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_618_, v___y_621_, v___y_622_, v___y_623_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v___x_650_; 
v_a_649_ = lean_ctor_get(v___x_648_, 1);
lean_inc(v_a_649_);
lean_dec_ref_known(v___x_648_, 2);
v___x_650_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_619_, v___y_621_, v___y_622_, v_a_649_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; 
v_a_651_ = lean_ctor_get(v___x_650_, 1);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 2);
v___y_625_ = v___y_620_;
v___y_626_ = v_a_651_;
goto v___jp_624_;
}
else
{
lean_object* v_a_652_; lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec_ref(v___y_620_);
lean_dec_ref(v_a_619_);
lean_dec_ref(v_f_618_);
v_a_652_ = lean_ctor_get(v___x_650_, 0);
v_a_653_ = lean_ctor_get(v___x_650_, 1);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_650_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_inc(v_a_652_);
lean_dec(v___x_650_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_652_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
else
{
lean_object* v_a_661_; lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec_ref(v___y_620_);
lean_dec_ref(v_a_619_);
lean_dec_ref(v_f_618_);
v_a_661_ = lean_ctor_get(v___x_648_, 0);
v_a_662_ = lean_ctor_get(v___x_648_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_648_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_inc(v_a_661_);
lean_dec(v___x_648_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_661_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
v___jp_624_:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = l_Lean_Expr_app___override(v_f_618_, v_a_619_);
v___x_628_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_627_, v___y_626_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_638_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
v_a_630_ = lean_ctor_get(v___x_628_, 1);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_638_ == 0)
{
v___x_632_ = v___x_628_;
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_inc(v_a_629_);
lean_dec(v___x_628_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v_a_629_);
lean_ctor_set(v___x_634_, 1, v___y_625_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_634_);
v___x_636_ = v___x_632_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_a_630_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
else
{
lean_object* v_a_639_; lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v___y_625_);
v_a_639_ = lean_ctor_get(v___x_628_, 0);
v_a_640_ = lean_ctor_get(v___x_628_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_628_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_inc(v_a_639_);
lean_dec(v___x_628_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_639_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1___boxed(lean_object* v_f_670_, lean_object* v_a_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
uint8_t v___y_33890__boxed_676_; lean_object* v_res_677_; 
v___y_33890__boxed_676_ = lean_unbox(v___y_673_);
v_res_677_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1(v_f_670_, v_a_671_, v___y_672_, v___y_33890__boxed_676_, v___y_674_, v___y_675_);
lean_dec_ref(v___y_674_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(lean_object* v_a_678_, lean_object* v_x_679_){
_start:
{
if (lean_obj_tag(v_x_679_) == 0)
{
lean_object* v___x_680_; 
v___x_680_ = lean_box(0);
return v___x_680_;
}
else
{
lean_object* v_key_681_; lean_object* v_value_682_; lean_object* v_tail_683_; lean_object* v_fst_684_; lean_object* v_snd_685_; lean_object* v_fst_686_; lean_object* v_snd_687_; size_t v___x_688_; size_t v___x_689_; uint8_t v___x_690_; 
v_key_681_ = lean_ctor_get(v_x_679_, 0);
v_value_682_ = lean_ctor_get(v_x_679_, 1);
v_tail_683_ = lean_ctor_get(v_x_679_, 2);
v_fst_684_ = lean_ctor_get(v_key_681_, 0);
v_snd_685_ = lean_ctor_get(v_key_681_, 1);
v_fst_686_ = lean_ctor_get(v_a_678_, 0);
v_snd_687_ = lean_ctor_get(v_a_678_, 1);
v___x_688_ = lean_ptr_addr(v_fst_684_);
v___x_689_ = lean_ptr_addr(v_fst_686_);
v___x_690_ = lean_usize_dec_eq(v___x_688_, v___x_689_);
if (v___x_690_ == 0)
{
v_x_679_ = v_tail_683_;
goto _start;
}
else
{
uint8_t v___x_692_; 
v___x_692_ = lean_nat_dec_eq(v_snd_685_, v_snd_687_);
if (v___x_692_ == 0)
{
v_x_679_ = v_tail_683_;
goto _start;
}
else
{
lean_object* v___x_694_; 
lean_inc(v_value_682_);
v___x_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_694_, 0, v_value_682_);
return v___x_694_;
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
lean_object* v___f_738_; lean_object* v___f_739_; lean_object* v___f_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___f_752_; lean_object* v___f_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_33404__overap_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
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
v___x_33404__overap_762_ = lean_panic_fn_borrowed(v___x_761_, v_msg_733_);
lean_dec(v___x_761_);
v___x_763_ = lean_box(v___y_735_);
lean_inc_ref(v___y_736_);
v___x_764_ = lean_apply_4(v___x_33404__overap_762_, v___y_734_, v___x_763_, v___y_736_, v___y_737_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___boxed(lean_object* v_msg_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
uint8_t v___y_34087__boxed_770_; lean_object* v_res_771_; 
v___y_34087__boxed_770_ = lean_unbox(v___y_767_);
v_res_771_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7(v_msg_765_, v___y_766_, v___y_34087__boxed_770_, v___y_768_, v___y_769_);
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
uint8_t v___y_34158__boxed_821_; lean_object* v_res_822_; 
v___y_34158__boxed_821_ = lean_unbox(v___y_818_);
v_res_822_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__6(v_structName_814_, v_idx_815_, v_struct_816_, v___y_817_, v___y_34158__boxed_821_, v___y_819_, v___y_820_);
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
uint8_t v_nondep_boxed_898_; uint8_t v___y_34241__boxed_899_; lean_object* v_res_900_; 
v_nondep_boxed_898_ = lean_unbox(v_nondep_893_);
v___y_34241__boxed_899_ = lean_unbox(v___y_895_);
v_res_900_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4(v_x_889_, v_t_890_, v_v_891_, v_b_892_, v_nondep_boxed_898_, v___y_894_, v___y_34241__boxed_899_, v___y_896_, v___y_897_);
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
uint8_t v_bi_boxed_963_; uint8_t v___y_34370__boxed_964_; lean_object* v_res_965_; 
v_bi_boxed_963_ = lean_unbox(v_bi_956_);
v___y_34370__boxed_964_ = lean_unbox(v___y_960_);
v_res_965_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2(v_x_955_, v_bi_boxed_963_, v_t_957_, v_b_958_, v___y_959_, v___y_34370__boxed_964_, v___y_961_, v___y_962_);
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
uint8_t v___y_34476__boxed_1013_; lean_object* v_res_1014_; 
v___y_34476__boxed_1013_ = lean_unbox(v___y_1010_);
v_res_1014_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__5(v_d_1007_, v_e_1008_, v___y_1009_, v___y_34476__boxed_1013_, v___y_1011_, v___y_1012_);
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
uint8_t v_bi_boxed_1077_; uint8_t v___y_34559__boxed_1078_; lean_object* v_res_1079_; 
v_bi_boxed_1077_ = lean_unbox(v_bi_1070_);
v___y_34559__boxed_1078_ = lean_unbox(v___y_1074_);
v_res_1079_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3(v_x_1069_, v_bi_boxed_1077_, v_t_1071_, v_b_1072_, v___y_1073_, v___y_34559__boxed_1078_, v___y_1075_, v___y_1076_);
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
lean_object* v_a_1105_; lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1130_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
v_a_1106_ = lean_ctor_get(v___x_1104_, 1);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1108_ = v___x_1104_;
v_isShared_1109_ = v_isSharedCheck_1130_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_inc(v_a_1105_);
lean_dec(v___x_1104_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1130_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_fst_1110_; lean_object* v_snd_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1129_; 
v_fst_1110_ = lean_ctor_get(v_a_1105_, 0);
v_snd_1111_ = lean_ctor_get(v_a_1105_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_a_1105_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1113_ = v_a_1105_;
v_isShared_1114_ = v_isSharedCheck_1129_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_snd_1111_);
lean_inc(v_fst_1110_);
lean_dec(v_a_1105_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1129_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
size_t v___x_1115_; size_t v___x_1116_; uint8_t v___x_1117_; 
v___x_1115_ = lean_ptr_addr(v_fn_1097_);
v___x_1116_ = lean_ptr_addr(v_fst_1102_);
v___x_1117_ = lean_usize_dec_eq(v___x_1115_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
lean_del_object(v___x_1113_);
lean_del_object(v___x_1108_);
lean_dec_ref_known(v_e_1091_, 2);
v___x_1118_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1(v_fst_1102_, v_fst_1110_, v_snd_1111_, v_a_1094_, v_a_1095_, v_a_1106_);
return v___x_1118_;
}
else
{
size_t v___x_1119_; size_t v___x_1120_; uint8_t v___x_1121_; 
v___x_1119_ = lean_ptr_addr(v_arg_1098_);
v___x_1120_ = lean_ptr_addr(v_fst_1110_);
v___x_1121_ = lean_usize_dec_eq(v___x_1119_, v___x_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; 
lean_del_object(v___x_1113_);
lean_del_object(v___x_1108_);
lean_dec_ref_known(v_e_1091_, 2);
v___x_1122_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1(v_fst_1102_, v_fst_1110_, v_snd_1111_, v_a_1094_, v_a_1095_, v_a_1106_);
return v___x_1122_;
}
else
{
lean_object* v___x_1124_; 
lean_dec(v_fst_1110_);
lean_dec(v_fst_1102_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v_e_1091_);
v___x_1124_ = v___x_1113_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_e_1091_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_snd_1111_);
v___x_1124_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1126_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1124_);
v___x_1126_ = v___x_1108_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_a_1106_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
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
lean_object* v_binderName_1131_; lean_object* v_binderType_1132_; lean_object* v_body_1133_; uint8_t v_binderInfo_1134_; lean_object* v___x_1135_; 
v_binderName_1131_ = lean_ctor_get(v_e_1091_, 0);
v_binderType_1132_ = lean_ctor_get(v_e_1091_, 1);
v_body_1133_ = lean_ctor_get(v_e_1091_, 2);
v_binderInfo_1134_ = lean_ctor_get_uint8(v_e_1091_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1092_);
lean_inc_ref(v_binderType_1132_);
v___x_1135_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1089_, v___x_1090_, v_binderType_1132_, v_offset_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v_a_1137_; lean_object* v_fst_1138_; lean_object* v_snd_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
v_a_1137_ = lean_ctor_get(v___x_1135_, 1);
lean_inc(v_a_1137_);
lean_dec_ref_known(v___x_1135_, 2);
v_fst_1138_ = lean_ctor_get(v_a_1136_, 0);
lean_inc(v_fst_1138_);
v_snd_1139_ = lean_ctor_get(v_a_1136_, 1);
lean_inc(v_snd_1139_);
lean_dec(v_a_1136_);
v___x_1140_ = lean_unsigned_to_nat(1u);
v___x_1141_ = lean_nat_add(v_offset_1092_, v___x_1140_);
lean_dec(v_offset_1092_);
lean_inc_ref(v_body_1133_);
v___x_1142_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1089_, v___x_1090_, v_body_1133_, v___x_1141_, v_snd_1139_, v_a_1094_, v_a_1095_, v_a_1137_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1168_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_a_1144_ = lean_ctor_get(v___x_1142_, 1);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1146_ = v___x_1142_;
v_isShared_1147_ = v_isSharedCheck_1168_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1168_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v_fst_1148_; lean_object* v_snd_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1167_; 
v_fst_1148_ = lean_ctor_get(v_a_1143_, 0);
v_snd_1149_ = lean_ctor_get(v_a_1143_, 1);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_a_1143_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1151_ = v_a_1143_;
v_isShared_1152_ = v_isSharedCheck_1167_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_snd_1149_);
lean_inc(v_fst_1148_);
lean_dec(v_a_1143_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1167_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
size_t v___x_1153_; size_t v___x_1154_; uint8_t v___x_1155_; 
v___x_1153_ = lean_ptr_addr(v_binderType_1132_);
v___x_1154_ = lean_ptr_addr(v_fst_1138_);
v___x_1155_ = lean_usize_dec_eq(v___x_1153_, v___x_1154_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
lean_inc(v_binderName_1131_);
lean_del_object(v___x_1151_);
lean_del_object(v___x_1146_);
lean_dec_ref_known(v_e_1091_, 3);
v___x_1156_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2(v_binderName_1131_, v_binderInfo_1134_, v_fst_1138_, v_fst_1148_, v_snd_1149_, v_a_1094_, v_a_1095_, v_a_1144_);
return v___x_1156_;
}
else
{
size_t v___x_1157_; size_t v___x_1158_; uint8_t v___x_1159_; 
v___x_1157_ = lean_ptr_addr(v_body_1133_);
v___x_1158_ = lean_ptr_addr(v_fst_1148_);
v___x_1159_ = lean_usize_dec_eq(v___x_1157_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
lean_inc(v_binderName_1131_);
lean_del_object(v___x_1151_);
lean_del_object(v___x_1146_);
lean_dec_ref_known(v_e_1091_, 3);
v___x_1160_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2(v_binderName_1131_, v_binderInfo_1134_, v_fst_1138_, v_fst_1148_, v_snd_1149_, v_a_1094_, v_a_1095_, v_a_1144_);
return v___x_1160_;
}
else
{
lean_object* v___x_1162_; 
lean_dec(v_fst_1148_);
lean_dec(v_fst_1138_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v_e_1091_);
v___x_1162_ = v___x_1151_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_e_1091_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_snd_1149_);
v___x_1162_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1164_; 
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1162_);
v___x_1164_ = v___x_1146_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_a_1144_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1138_);
lean_dec_ref_known(v_e_1091_, 3);
return v___x_1142_;
}
}
else
{
lean_dec_ref_known(v_e_1091_, 3);
lean_dec(v_offset_1092_);
return v___x_1135_;
}
}
case 7:
{
lean_object* v_binderName_1169_; lean_object* v_binderType_1170_; lean_object* v_body_1171_; uint8_t v_binderInfo_1172_; lean_object* v___x_1173_; 
v_binderName_1169_ = lean_ctor_get(v_e_1091_, 0);
v_binderType_1170_ = lean_ctor_get(v_e_1091_, 1);
v_body_1171_ = lean_ctor_get(v_e_1091_, 2);
v_binderInfo_1172_ = lean_ctor_get_uint8(v_e_1091_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1092_);
lean_inc_ref(v_binderType_1170_);
v___x_1173_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1089_, v___x_1090_, v_binderType_1170_, v_offset_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v_a_1175_; lean_object* v_fst_1176_; lean_object* v_snd_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1174_);
v_a_1175_ = lean_ctor_get(v___x_1173_, 1);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1173_, 2);
v_fst_1176_ = lean_ctor_get(v_a_1174_, 0);
lean_inc(v_fst_1176_);
v_snd_1177_ = lean_ctor_get(v_a_1174_, 1);
lean_inc(v_snd_1177_);
lean_dec(v_a_1174_);
v___x_1178_ = lean_unsigned_to_nat(1u);
v___x_1179_ = lean_nat_add(v_offset_1092_, v___x_1178_);
lean_dec(v_offset_1092_);
lean_inc_ref(v_body_1171_);
v___x_1180_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1089_, v___x_1090_, v_body_1171_, v___x_1179_, v_snd_1177_, v_a_1094_, v_a_1095_, v_a_1175_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1206_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
v_a_1182_ = lean_ctor_get(v___x_1180_, 1);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1184_ = v___x_1180_;
v_isShared_1185_ = v_isSharedCheck_1206_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_inc(v_a_1181_);
lean_dec(v___x_1180_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1206_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v_fst_1186_; lean_object* v_snd_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1205_; 
v_fst_1186_ = lean_ctor_get(v_a_1181_, 0);
v_snd_1187_ = lean_ctor_get(v_a_1181_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_a_1181_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1189_ = v_a_1181_;
v_isShared_1190_ = v_isSharedCheck_1205_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_snd_1187_);
lean_inc(v_fst_1186_);
lean_dec(v_a_1181_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1205_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
size_t v___x_1191_; size_t v___x_1192_; uint8_t v___x_1193_; 
v___x_1191_ = lean_ptr_addr(v_binderType_1170_);
v___x_1192_ = lean_ptr_addr(v_fst_1176_);
v___x_1193_ = lean_usize_dec_eq(v___x_1191_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
lean_inc(v_binderName_1169_);
lean_del_object(v___x_1189_);
lean_del_object(v___x_1184_);
lean_dec_ref_known(v_e_1091_, 3);
v___x_1194_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3(v_binderName_1169_, v_binderInfo_1172_, v_fst_1176_, v_fst_1186_, v_snd_1187_, v_a_1094_, v_a_1095_, v_a_1182_);
return v___x_1194_;
}
else
{
size_t v___x_1195_; size_t v___x_1196_; uint8_t v___x_1197_; 
v___x_1195_ = lean_ptr_addr(v_body_1171_);
v___x_1196_ = lean_ptr_addr(v_fst_1186_);
v___x_1197_ = lean_usize_dec_eq(v___x_1195_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; 
lean_inc(v_binderName_1169_);
lean_del_object(v___x_1189_);
lean_del_object(v___x_1184_);
lean_dec_ref_known(v_e_1091_, 3);
v___x_1198_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3(v_binderName_1169_, v_binderInfo_1172_, v_fst_1176_, v_fst_1186_, v_snd_1187_, v_a_1094_, v_a_1095_, v_a_1182_);
return v___x_1198_;
}
else
{
lean_object* v___x_1200_; 
lean_dec(v_fst_1186_);
lean_dec(v_fst_1176_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v_e_1091_);
v___x_1200_ = v___x_1189_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_e_1091_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_snd_1187_);
v___x_1200_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1202_; 
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1200_);
v___x_1202_ = v___x_1184_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_a_1182_);
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
}
}
else
{
lean_dec(v_fst_1176_);
lean_dec_ref_known(v_e_1091_, 3);
return v___x_1180_;
}
}
else
{
lean_dec_ref_known(v_e_1091_, 3);
lean_dec(v_offset_1092_);
return v___x_1173_;
}
}
case 8:
{
lean_object* v_declName_1207_; lean_object* v_type_1208_; lean_object* v_value_1209_; lean_object* v_body_1210_; uint8_t v_nondep_1211_; lean_object* v___x_1212_; 
v_declName_1207_ = lean_ctor_get(v_e_1091_, 0);
v_type_1208_ = lean_ctor_get(v_e_1091_, 1);
v_value_1209_ = lean_ctor_get(v_e_1091_, 2);
v_body_1210_ = lean_ctor_get(v_e_1091_, 3);
v_nondep_1211_ = lean_ctor_get_uint8(v_e_1091_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1092_);
lean_inc_ref(v_type_1208_);
v___x_1212_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1089_, v___x_1090_, v_type_1208_, v_offset_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v_a_1214_; lean_object* v_fst_1215_; lean_object* v_snd_1216_; lean_object* v___x_1217_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
v_a_1214_ = lean_ctor_get(v___x_1212_, 1);
lean_inc(v_a_1214_);
lean_dec_ref_known(v___x_1212_, 2);
v_fst_1215_ = lean_ctor_get(v_a_1213_, 0);
lean_inc(v_fst_1215_);
v_snd_1216_ = lean_ctor_get(v_a_1213_, 1);
lean_inc(v_snd_1216_);
lean_dec(v_a_1213_);
lean_inc(v_offset_1092_);
lean_inc_ref(v_value_1209_);
v___x_1217_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1089_, v___x_1090_, v_value_1209_, v_offset_1092_, v_snd_1216_, v_a_1094_, v_a_1095_, v_a_1214_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v_a_1219_; lean_object* v_fst_1220_; lean_object* v_snd_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
v_a_1219_ = lean_ctor_get(v___x_1217_, 1);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1217_, 2);
v_fst_1220_ = lean_ctor_get(v_a_1218_, 0);
lean_inc(v_fst_1220_);
v_snd_1221_ = lean_ctor_get(v_a_1218_, 1);
lean_inc(v_snd_1221_);
lean_dec(v_a_1218_);
v___x_1222_ = lean_unsigned_to_nat(1u);
v___x_1223_ = lean_nat_add(v_offset_1092_, v___x_1222_);
lean_dec(v_offset_1092_);
lean_inc_ref(v_body_1210_);
v___x_1224_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1089_, v___x_1090_, v_body_1210_, v___x_1223_, v_snd_1221_, v_a_1094_, v_a_1095_, v_a_1219_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1254_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
v_a_1226_ = lean_ctor_get(v___x_1224_, 1);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1228_ = v___x_1224_;
v_isShared_1229_ = v_isSharedCheck_1254_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_inc(v_a_1225_);
lean_dec(v___x_1224_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1254_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v_fst_1230_; lean_object* v_snd_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1253_; 
v_fst_1230_ = lean_ctor_get(v_a_1225_, 0);
v_snd_1231_ = lean_ctor_get(v_a_1225_, 1);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_a_1225_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1233_ = v_a_1225_;
v_isShared_1234_ = v_isSharedCheck_1253_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_snd_1231_);
lean_inc(v_fst_1230_);
lean_dec(v_a_1225_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1253_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
size_t v___x_1235_; size_t v___x_1236_; uint8_t v___x_1237_; 
v___x_1235_ = lean_ptr_addr(v_type_1208_);
v___x_1236_ = lean_ptr_addr(v_fst_1215_);
v___x_1237_ = lean_usize_dec_eq(v___x_1235_, v___x_1236_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; 
lean_inc(v_declName_1207_);
lean_del_object(v___x_1233_);
lean_del_object(v___x_1228_);
lean_dec_ref_known(v_e_1091_, 4);
v___x_1238_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4(v_declName_1207_, v_fst_1215_, v_fst_1220_, v_fst_1230_, v_nondep_1211_, v_snd_1231_, v_a_1094_, v_a_1095_, v_a_1226_);
return v___x_1238_;
}
else
{
size_t v___x_1239_; size_t v___x_1240_; uint8_t v___x_1241_; 
v___x_1239_ = lean_ptr_addr(v_value_1209_);
v___x_1240_ = lean_ptr_addr(v_fst_1220_);
v___x_1241_ = lean_usize_dec_eq(v___x_1239_, v___x_1240_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; 
lean_inc(v_declName_1207_);
lean_del_object(v___x_1233_);
lean_del_object(v___x_1228_);
lean_dec_ref_known(v_e_1091_, 4);
v___x_1242_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4(v_declName_1207_, v_fst_1215_, v_fst_1220_, v_fst_1230_, v_nondep_1211_, v_snd_1231_, v_a_1094_, v_a_1095_, v_a_1226_);
return v___x_1242_;
}
else
{
size_t v___x_1243_; size_t v___x_1244_; uint8_t v___x_1245_; 
v___x_1243_ = lean_ptr_addr(v_body_1210_);
v___x_1244_ = lean_ptr_addr(v_fst_1230_);
v___x_1245_ = lean_usize_dec_eq(v___x_1243_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; 
lean_inc(v_declName_1207_);
lean_del_object(v___x_1233_);
lean_del_object(v___x_1228_);
lean_dec_ref_known(v_e_1091_, 4);
v___x_1246_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4(v_declName_1207_, v_fst_1215_, v_fst_1220_, v_fst_1230_, v_nondep_1211_, v_snd_1231_, v_a_1094_, v_a_1095_, v_a_1226_);
return v___x_1246_;
}
else
{
lean_object* v___x_1248_; 
lean_dec(v_fst_1230_);
lean_dec(v_fst_1220_);
lean_dec(v_fst_1215_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v_e_1091_);
v___x_1248_ = v___x_1233_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_e_1091_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_snd_1231_);
v___x_1248_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1250_; 
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1248_);
v___x_1250_ = v___x_1228_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_a_1226_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
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
lean_dec(v_fst_1220_);
lean_dec(v_fst_1215_);
lean_dec_ref_known(v_e_1091_, 4);
return v___x_1224_;
}
}
else
{
lean_dec(v_fst_1215_);
lean_dec_ref_known(v_e_1091_, 4);
lean_dec(v_offset_1092_);
return v___x_1217_;
}
}
else
{
lean_dec_ref_known(v_e_1091_, 4);
lean_dec(v_offset_1092_);
return v___x_1212_;
}
}
case 10:
{
lean_object* v_data_1255_; lean_object* v_expr_1256_; lean_object* v___x_1257_; 
v_data_1255_ = lean_ctor_get(v_e_1091_, 0);
v_expr_1256_ = lean_ctor_get(v_e_1091_, 1);
lean_inc_ref(v_expr_1256_);
v___x_1257_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1089_, v___x_1090_, v_expr_1256_, v_offset_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1279_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
v_a_1259_ = lean_ctor_get(v___x_1257_, 1);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1261_ = v___x_1257_;
v_isShared_1262_ = v_isSharedCheck_1279_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_inc(v_a_1258_);
lean_dec(v___x_1257_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1279_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v_fst_1263_; lean_object* v_snd_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1278_; 
v_fst_1263_ = lean_ctor_get(v_a_1258_, 0);
v_snd_1264_ = lean_ctor_get(v_a_1258_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_a_1258_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1266_ = v_a_1258_;
v_isShared_1267_ = v_isSharedCheck_1278_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_snd_1264_);
lean_inc(v_fst_1263_);
lean_dec(v_a_1258_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1278_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
size_t v___x_1268_; size_t v___x_1269_; uint8_t v___x_1270_; 
v___x_1268_ = lean_ptr_addr(v_expr_1256_);
v___x_1269_ = lean_ptr_addr(v_fst_1263_);
v___x_1270_ = lean_usize_dec_eq(v___x_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; 
lean_inc(v_data_1255_);
lean_del_object(v___x_1266_);
lean_del_object(v___x_1261_);
lean_dec_ref_known(v_e_1091_, 2);
v___x_1271_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__5(v_data_1255_, v_fst_1263_, v_snd_1264_, v_a_1094_, v_a_1095_, v_a_1259_);
return v___x_1271_;
}
else
{
lean_object* v___x_1273_; 
lean_dec(v_fst_1263_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v_e_1091_);
v___x_1273_ = v___x_1266_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_e_1091_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_snd_1264_);
v___x_1273_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1275_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v___x_1273_);
v___x_1275_ = v___x_1261_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_a_1259_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1091_, 2);
return v___x_1257_;
}
}
case 11:
{
lean_object* v_typeName_1280_; lean_object* v_idx_1281_; lean_object* v_struct_1282_; lean_object* v___x_1283_; 
v_typeName_1280_ = lean_ctor_get(v_e_1091_, 0);
v_idx_1281_ = lean_ctor_get(v_e_1091_, 1);
v_struct_1282_ = lean_ctor_get(v_e_1091_, 2);
lean_inc_ref(v_struct_1282_);
v___x_1283_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1089_, v___x_1090_, v_struct_1282_, v_offset_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1305_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_a_1285_ = lean_ctor_get(v___x_1283_, 1);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1287_ = v___x_1283_;
v_isShared_1288_ = v_isSharedCheck_1305_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1305_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v_fst_1289_; lean_object* v_snd_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1304_; 
v_fst_1289_ = lean_ctor_get(v_a_1284_, 0);
v_snd_1290_ = lean_ctor_get(v_a_1284_, 1);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_a_1284_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1292_ = v_a_1284_;
v_isShared_1293_ = v_isSharedCheck_1304_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_snd_1290_);
lean_inc(v_fst_1289_);
lean_dec(v_a_1284_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1304_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
size_t v___x_1294_; size_t v___x_1295_; uint8_t v___x_1296_; 
v___x_1294_ = lean_ptr_addr(v_struct_1282_);
v___x_1295_ = lean_ptr_addr(v_fst_1289_);
v___x_1296_ = lean_usize_dec_eq(v___x_1294_, v___x_1295_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; 
lean_inc(v_idx_1281_);
lean_inc(v_typeName_1280_);
lean_del_object(v___x_1292_);
lean_del_object(v___x_1287_);
lean_dec_ref_known(v_e_1091_, 3);
v___x_1297_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__6(v_typeName_1280_, v_idx_1281_, v_fst_1289_, v_snd_1290_, v_a_1094_, v_a_1095_, v_a_1285_);
return v___x_1297_;
}
else
{
lean_object* v___x_1299_; 
lean_dec(v_fst_1289_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v_e_1091_);
v___x_1299_ = v___x_1292_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_e_1091_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_snd_1290_);
v___x_1299_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1301_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1299_);
v___x_1301_ = v___x_1287_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_a_1285_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1091_, 3);
return v___x_1283_;
}
}
default: 
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
lean_dec(v_offset_1092_);
lean_dec_ref(v_e_1091_);
v___x_1306_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__3);
v___x_1307_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7(v___x_1306_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
return v___x_1307_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(lean_object* v___x_1308_, lean_object* v___x_1309_, lean_object* v_e_1310_, lean_object* v_offset_1311_, lean_object* v_a_1312_, uint8_t v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v_key_1316_; lean_object* v___x_1317_; 
lean_inc(v_offset_1311_);
lean_inc_ref(v_e_1310_);
v_key_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1316_, 0, v_e_1310_);
lean_ctor_set(v_key_1316_, 1, v_offset_1311_);
v___x_1317_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___redArg(v_a_1312_, v_key_1316_);
if (lean_obj_tag(v___x_1317_) == 1)
{
lean_object* v_val_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
lean_dec_ref_known(v_key_1316_, 2);
lean_dec(v_offset_1311_);
lean_dec_ref(v_e_1310_);
v_val_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_val_1318_);
lean_dec_ref_known(v___x_1317_, 1);
v___x_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1319_, 0, v_val_1318_);
lean_ctor_set(v___x_1319_, 1, v_a_1312_);
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v_a_1315_);
return v___x_1320_;
}
else
{
lean_dec(v___x_1317_);
switch(lean_obj_tag(v_e_1310_))
{
case 0:
{
lean_object* v_deBruijnIndex_1321_; uint8_t v___x_1322_; 
v_deBruijnIndex_1321_ = lean_ctor_get(v_e_1310_, 0);
v___x_1322_ = lean_nat_dec_le(v_offset_1311_, v_deBruijnIndex_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; 
lean_dec(v_offset_1311_);
v___x_1323_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1316_, v_e_1310_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
return v___x_1323_;
}
else
{
lean_object* v_size_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
lean_inc(v_deBruijnIndex_1321_);
lean_dec_ref_known(v_e_1310_, 1);
v_size_1324_ = lean_ctor_get(v___x_1309_, 2);
v___x_1325_ = l_Lean_instInhabitedExpr;
v___x_1326_ = lean_nat_sub(v_deBruijnIndex_1321_, v_offset_1311_);
lean_dec(v_offset_1311_);
lean_dec(v_deBruijnIndex_1321_);
v___x_1327_ = lean_nat_sub(v___x_1308_, v___x_1326_);
lean_dec(v___x_1326_);
v___x_1328_ = lean_unsigned_to_nat(1u);
v___x_1329_ = lean_nat_sub(v___x_1327_, v___x_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_nat_dec_lt(v___x_1329_, v_size_1324_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_dec(v___x_1329_);
v___x_1331_ = l_outOfBounds___redArg(v___x_1325_);
v___x_1332_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1316_, v___x_1331_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
return v___x_1332_;
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1325_, v___x_1309_, v___x_1329_);
lean_dec(v___x_1329_);
v___x_1334_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1316_, v___x_1333_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
return v___x_1334_;
}
}
}
case 9:
{
lean_object* v___x_1335_; 
lean_dec(v_offset_1311_);
v___x_1335_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1316_, v_e_1310_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
return v___x_1335_;
}
case 2:
{
lean_object* v___x_1336_; 
lean_dec(v_offset_1311_);
v___x_1336_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1316_, v_e_1310_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
return v___x_1336_;
}
case 1:
{
lean_object* v___x_1337_; 
lean_dec(v_offset_1311_);
v___x_1337_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1316_, v_e_1310_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
return v___x_1337_;
}
case 4:
{
lean_object* v___x_1338_; 
lean_dec(v_offset_1311_);
v___x_1338_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1316_, v_e_1310_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
return v___x_1338_;
}
case 3:
{
lean_object* v___x_1339_; 
lean_dec(v_offset_1311_);
v___x_1339_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1316_, v_e_1310_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
return v___x_1339_;
}
default: 
{
lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1340_ = l_Lean_Expr_looseBVarRange(v_e_1310_);
v___x_1341_ = lean_nat_dec_le(v___x_1340_, v_offset_1311_);
lean_dec(v___x_1340_);
if (v___x_1341_ == 0)
{
switch(lean_obj_tag(v_e_1310_))
{
case 9:
{
lean_object* v___x_1342_; 
lean_dec(v_offset_1311_);
v___x_1342_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1316_, v_e_1310_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
return v___x_1342_;
}
case 2:
{
lean_object* v___x_1343_; 
lean_dec(v_offset_1311_);
v___x_1343_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1316_, v_e_1310_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
return v___x_1343_;
}
case 0:
{
lean_object* v___x_1344_; 
lean_dec(v_offset_1311_);
v___x_1344_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1316_, v_e_1310_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
return v___x_1344_;
}
case 1:
{
lean_object* v___x_1345_; 
lean_dec(v_offset_1311_);
v___x_1345_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1316_, v_e_1310_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
return v___x_1345_;
}
case 4:
{
lean_object* v___x_1346_; 
lean_dec(v_offset_1311_);
v___x_1346_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1316_, v_e_1310_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
return v___x_1346_;
}
case 3:
{
lean_object* v___x_1347_; 
lean_dec(v_offset_1311_);
v___x_1347_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1316_, v_e_1310_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
return v___x_1347_;
}
default: 
{
lean_object* v___x_1348_; 
v___x_1348_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0(v___x_1308_, v___x_1309_, v_e_1310_, v_offset_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v_a_1350_; lean_object* v_fst_1351_; lean_object* v_snd_1352_; lean_object* v___x_1353_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
v_a_1350_ = lean_ctor_get(v___x_1348_, 1);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1348_, 2);
v_fst_1351_ = lean_ctor_get(v_a_1349_, 0);
lean_inc(v_fst_1351_);
v_snd_1352_ = lean_ctor_get(v_a_1349_, 1);
lean_inc(v_snd_1352_);
lean_dec(v_a_1349_);
v___x_1353_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1316_, v_fst_1351_, v_snd_1352_, v_a_1313_, v_a_1314_, v_a_1350_);
return v___x_1353_;
}
else
{
lean_dec_ref_known(v_key_1316_, 2);
return v___x_1348_;
}
}
}
}
else
{
lean_object* v___x_1354_; 
lean_dec(v_offset_1311_);
v___x_1354_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1316_, v_e_1310_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
return v___x_1354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0___boxed(lean_object* v___x_1355_, lean_object* v___x_1356_, lean_object* v_e_1357_, lean_object* v_offset_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
uint8_t v_a_boxed_1363_; lean_object* v_res_1364_; 
v_a_boxed_1363_ = lean_unbox(v_a_1360_);
v_res_1364_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1355_, v___x_1356_, v_e_1357_, v_offset_1358_, v_a_1359_, v_a_boxed_1363_, v_a_1361_, v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec_ref(v___x_1356_);
lean_dec(v___x_1355_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___boxed(lean_object* v___x_1365_, lean_object* v___x_1366_, lean_object* v_e_1367_, lean_object* v_offset_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
uint8_t v_a_boxed_1373_; lean_object* v_res_1374_; 
v_a_boxed_1373_ = lean_unbox(v_a_1370_);
v_res_1374_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0(v___x_1365_, v___x_1366_, v_e_1367_, v_offset_1368_, v_a_1369_, v_a_boxed_1373_, v_a_1371_, v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec_ref(v___x_1366_);
lean_dec(v___x_1365_);
return v_res_1374_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = lean_box(0);
v___x_1376_ = lean_unsigned_to_nat(16u);
v___x_1377_ = lean_mk_array(v___x_1376_, v___x_1375_);
return v___x_1377_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1378_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__0, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__0);
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
lean_ctor_set(v___x_1380_, 1, v___x_1378_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0(lean_object* v_e_1381_, lean_object* v_size_1382_, lean_object* v___x_1383_, lean_object* v_xs_1384_, uint8_t v_debug_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1381_))
{
case 0:
{
lean_object* v_deBruijnIndex_1389_; uint8_t v___x_1390_; 
v_deBruijnIndex_1389_ = lean_ctor_get(v_e_1381_, 0);
v___x_1390_ = lean_nat_dec_le(v___x_1388_, v_deBruijnIndex_1389_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1391_, 0, v_e_1381_);
lean_ctor_set(v___x_1391_, 1, v___y_1387_);
return v___x_1391_;
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
lean_inc(v_deBruijnIndex_1389_);
lean_dec_ref_known(v_e_1381_, 1);
v___x_1392_ = lean_nat_sub(v_size_1382_, v_deBruijnIndex_1389_);
lean_dec(v_deBruijnIndex_1389_);
v___x_1393_ = lean_unsigned_to_nat(1u);
v___x_1394_ = lean_nat_sub(v___x_1392_, v___x_1393_);
lean_dec(v___x_1392_);
v___x_1395_ = lean_nat_dec_lt(v___x_1394_, v_size_1382_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
lean_dec(v___x_1394_);
v___x_1396_ = l_outOfBounds___redArg(v___x_1383_);
v___x_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
lean_ctor_set(v___x_1397_, 1, v___y_1387_);
return v___x_1397_;
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1383_, v_xs_1384_, v___x_1394_);
lean_dec(v___x_1394_);
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
lean_ctor_set(v___x_1399_, 1, v___y_1387_);
return v___x_1399_;
}
}
}
case 9:
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1400_, 0, v_e_1381_);
lean_ctor_set(v___x_1400_, 1, v___y_1387_);
return v___x_1400_;
}
case 2:
{
lean_object* v___x_1401_; 
v___x_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1401_, 0, v_e_1381_);
lean_ctor_set(v___x_1401_, 1, v___y_1387_);
return v___x_1401_;
}
case 1:
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_e_1381_);
lean_ctor_set(v___x_1402_, 1, v___y_1387_);
return v___x_1402_;
}
case 4:
{
lean_object* v___x_1403_; 
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v_e_1381_);
lean_ctor_set(v___x_1403_, 1, v___y_1387_);
return v___x_1403_;
}
case 3:
{
lean_object* v___x_1404_; 
v___x_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1404_, 0, v_e_1381_);
lean_ctor_set(v___x_1404_, 1, v___y_1387_);
return v___x_1404_;
}
default: 
{
lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1405_ = l_Lean_Expr_looseBVarRange(v_e_1381_);
v___x_1406_ = lean_nat_dec_le(v___x_1405_, v___x_1388_);
lean_dec(v___x_1405_);
if (v___x_1406_ == 0)
{
switch(lean_obj_tag(v_e_1381_))
{
case 9:
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v_e_1381_);
lean_ctor_set(v___x_1407_, 1, v___y_1387_);
return v___x_1407_;
}
case 2:
{
lean_object* v___x_1408_; 
v___x_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1408_, 0, v_e_1381_);
lean_ctor_set(v___x_1408_, 1, v___y_1387_);
return v___x_1408_;
}
case 0:
{
lean_object* v___x_1409_; 
v___x_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1409_, 0, v_e_1381_);
lean_ctor_set(v___x_1409_, 1, v___y_1387_);
return v___x_1409_;
}
case 1:
{
lean_object* v___x_1410_; 
v___x_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1410_, 0, v_e_1381_);
lean_ctor_set(v___x_1410_, 1, v___y_1387_);
return v___x_1410_;
}
case 4:
{
lean_object* v___x_1411_; 
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v_e_1381_);
lean_ctor_set(v___x_1411_, 1, v___y_1387_);
return v___x_1411_;
}
case 3:
{
lean_object* v___x_1412_; 
v___x_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1412_, 0, v_e_1381_);
lean_ctor_set(v___x_1412_, 1, v___y_1387_);
return v___x_1412_;
}
default: 
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__1);
v___x_1414_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0(v_size_1382_, v_xs_1384_, v_e_1381_, v___x_1388_, v___x_1413_, v_debug_1385_, v___y_1386_, v___y_1387_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1424_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_a_1416_ = lean_ctor_get(v___x_1414_, 1);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1418_ = v___x_1414_;
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v_fst_1420_; lean_object* v___x_1422_; 
v_fst_1420_ = lean_ctor_get(v_a_1415_, 0);
lean_inc(v_fst_1420_);
lean_dec(v_a_1415_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v_fst_1420_);
v___x_1422_ = v___x_1418_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_fst_1420_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_a_1416_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
v_a_1425_ = lean_ctor_get(v___x_1414_, 0);
v_a_1426_ = lean_ctor_get(v___x_1414_, 1);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1414_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_inc(v_a_1425_);
lean_dec(v___x_1414_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1425_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
}
else
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1434_, 0, v_e_1381_);
lean_ctor_set(v___x_1434_, 1, v___y_1387_);
return v___x_1434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___boxed(lean_object* v_e_1435_, lean_object* v_size_1436_, lean_object* v___x_1437_, lean_object* v_xs_1438_, lean_object* v_debug_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
uint8_t v_debug_boxed_1442_; lean_object* v_res_1443_; 
v_debug_boxed_1442_ = lean_unbox(v_debug_1439_);
v_res_1443_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0(v_e_1435_, v_size_1436_, v___x_1437_, v_xs_1438_, v_debug_boxed_1442_, v___y_1440_, v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec_ref(v_xs_1438_);
lean_dec_ref(v___x_1437_);
lean_dec(v_size_1436_);
return v_res_1443_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__2(void){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1446_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_1447_ = lean_unsigned_to_nat(16u);
v___x_1448_ = lean_unsigned_to_nat(62u);
v___x_1449_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__1));
v___x_1450_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__0));
v___x_1451_ = l_mkPanicMessageWithDecl(v___x_1450_, v___x_1449_, v___x_1448_, v___x_1447_, v___x_1446_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(lean_object* v_e_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v_a_1463_; uint8_t v___x_1481_; 
v___x_1481_ = l_Lean_Expr_hasLooseBVars(v_e_1452_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; 
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v_e_1452_);
return v___x_1482_;
}
else
{
lean_object* v___x_1483_; uint8_t v___x_1484_; lean_object* v___x_1485_; lean_object* v_subst_1486_; lean_object* v___x_1487_; 
v___x_1483_ = l_Lean_instInhabitedExpr;
v___x_1484_ = 0;
v___x_1485_ = lean_st_ref_get(v_a_1454_);
v_subst_1486_ = lean_ctor_get(v___x_1485_, 2);
lean_inc_ref(v_subst_1486_);
lean_dec(v___x_1485_);
v___x_1487_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_subst_1486_, v_e_1452_);
lean_dec_ref(v_subst_1486_);
if (lean_obj_tag(v___x_1487_) == 1)
{
lean_object* v_val_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec_ref(v_e_1452_);
v_val_1488_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1487_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_val_1488_);
lean_dec(v___x_1487_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set_tag(v___x_1490_, 0);
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_val_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
else
{
lean_object* v_xs_1496_; lean_object* v_size_1497_; lean_object* v___x_1498_; uint8_t v_debug_1499_; lean_object* v___x_1500_; lean_object* v___f_1501_; lean_object* v___x_1502_; lean_object* v_env_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec(v___x_1487_);
v_xs_1496_ = lean_ctor_get(v_a_1453_, 0);
v_size_1497_ = lean_ctor_get(v_xs_1496_, 2);
v___x_1498_ = lean_st_ref_get(v_a_1456_);
v_debug_1499_ = lean_ctor_get_uint8(v___x_1498_, sizeof(void*)*11);
lean_dec(v___x_1498_);
v___x_1500_ = lean_box(v_debug_1499_);
lean_inc_ref(v_xs_1496_);
lean_inc(v_size_1497_);
lean_inc_ref(v_e_1452_);
v___f_1501_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___boxed), 7, 5);
lean_closure_set(v___f_1501_, 0, v_e_1452_);
lean_closure_set(v___f_1501_, 1, v_size_1497_);
lean_closure_set(v___f_1501_, 2, v___x_1483_);
lean_closure_set(v___f_1501_, 3, v_xs_1496_);
lean_closure_set(v___f_1501_, 4, v___x_1500_);
v___x_1502_ = lean_st_ref_get(v_a_1460_);
v_env_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc_ref(v_env_1503_);
lean_dec(v___x_1502_);
v___x_1504_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1504_, 0, v_env_1503_);
lean_ctor_set_uint8(v___x_1504_, sizeof(void*)*1, v___x_1484_);
lean_ctor_set_uint8(v___x_1504_, sizeof(void*)*1 + 1, v___x_1484_);
v___x_1505_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1501_, v___x_1504_, v_a_1456_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref_known(v___x_1505_, 1);
if (lean_obj_tag(v_a_1506_) == 0)
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
lean_dec_ref_known(v_a_1506_, 1);
v___x_1507_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__2, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__2_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__2);
v___x_1508_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1(v___x_1507_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_a_1509_);
lean_dec_ref_known(v___x_1508_, 1);
v_a_1463_ = v_a_1509_;
goto v___jp_1462_;
}
else
{
lean_dec_ref(v_e_1452_);
return v___x_1508_;
}
}
else
{
lean_object* v_a_1510_; 
v_a_1510_ = lean_ctor_get(v_a_1506_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v_a_1506_, 1);
v_a_1463_ = v_a_1510_;
goto v___jp_1462_;
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec_ref(v_e_1452_);
v_a_1511_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1505_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1505_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
v___jp_1462_:
{
lean_object* v___x_1464_; lean_object* v_visited_1465_; lean_object* v_types_1466_; lean_object* v_subst_1467_; lean_object* v_visitedClosed_1468_; lean_object* v_hasDepLetCache_1469_; lean_object* v_numConverted_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1480_; 
v___x_1464_ = lean_st_ref_take(v_a_1454_);
v_visited_1465_ = lean_ctor_get(v___x_1464_, 0);
v_types_1466_ = lean_ctor_get(v___x_1464_, 1);
v_subst_1467_ = lean_ctor_get(v___x_1464_, 2);
v_visitedClosed_1468_ = lean_ctor_get(v___x_1464_, 3);
v_hasDepLetCache_1469_ = lean_ctor_get(v___x_1464_, 4);
v_numConverted_1470_ = lean_ctor_get(v___x_1464_, 5);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1472_ = v___x_1464_;
v_isShared_1473_ = v_isSharedCheck_1480_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_numConverted_1470_);
lean_inc(v_hasDepLetCache_1469_);
lean_inc(v_visitedClosed_1468_);
lean_inc(v_subst_1467_);
lean_inc(v_types_1466_);
lean_inc(v_visited_1465_);
lean_dec(v___x_1464_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1480_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
lean_inc_ref(v_a_1463_);
v___x_1474_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_subst_1467_, v_e_1452_, v_a_1463_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 2, v___x_1474_);
v___x_1476_ = v___x_1472_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_visited_1465_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_types_1466_);
lean_ctor_set(v_reuseFailAlloc_1479_, 2, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1479_, 3, v_visitedClosed_1468_);
lean_ctor_set(v_reuseFailAlloc_1479_, 4, v_hasDepLetCache_1469_);
lean_ctor_set(v_reuseFailAlloc_1479_, 5, v_numConverted_1470_);
v___x_1476_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = lean_st_ref_put(v_a_1454_, v___x_1476_);
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v_a_1463_);
return v___x_1478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___boxed(lean_object* v_e_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_e_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
lean_dec(v_a_1523_);
lean_dec_ref(v_a_1522_);
lean_dec(v_a_1521_);
lean_dec_ref(v_a_1520_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1530_, lean_object* v_m_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___redArg(v_m_1531_, v_a_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1534_, lean_object* v_m_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2(v_00_u03b2_1534_, v_m_1535_, v_a_1536_);
lean_dec_ref(v_a_1536_);
lean_dec_ref(v_m_1535_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_1538_, lean_object* v_a_1539_, lean_object* v_x_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_1539_, v_x_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_1542_, lean_object* v_a_1543_, lean_object* v_x_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10(v_00_u03b2_1542_, v_a_1543_, v_x_1544_);
lean_dec(v_x_1544_);
lean_dec_ref(v_a_1543_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(lean_object* v_msgData_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v___x_1552_; lean_object* v_env_1553_; lean_object* v___x_1554_; lean_object* v_toCold_1555_; lean_object* v_mctx_1556_; lean_object* v_lctx_1557_; lean_object* v_options_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1552_ = lean_st_ref_get(v___y_1550_);
v_env_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc_ref(v_env_1553_);
lean_dec(v___x_1552_);
v___x_1554_ = lean_st_ref_get(v___y_1548_);
v_toCold_1555_ = lean_ctor_get(v___y_1549_, 0);
v_mctx_1556_ = lean_ctor_get(v___x_1554_, 0);
lean_inc_ref(v_mctx_1556_);
lean_dec(v___x_1554_);
v_lctx_1557_ = lean_ctor_get(v___y_1547_, 2);
v_options_1558_ = lean_ctor_get(v_toCold_1555_, 2);
lean_inc_ref(v_options_1558_);
lean_inc_ref(v_lctx_1557_);
v___x_1559_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1559_, 0, v_env_1553_);
lean_ctor_set(v___x_1559_, 1, v_mctx_1556_);
lean_ctor_set(v___x_1559_, 2, v_lctx_1557_);
lean_ctor_set(v___x_1559_, 3, v_options_1558_);
v___x_1560_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
lean_ctor_set(v___x_1560_, 1, v_msgData_1546_);
v___x_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0___boxed(lean_object* v_msgData_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(v_msgData_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(lean_object* v_msg_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_ref_1575_; lean_object* v___x_1576_; lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1585_; 
v_ref_1575_ = lean_ctor_get(v___y_1572_, 2);
v___x_1576_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(v_msg_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1585_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1585_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; lean_object* v___x_1583_; 
lean_inc(v_ref_1575_);
v___x_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1581_, 0, v_ref_1575_);
lean_ctor_set(v___x_1581_, 1, v_a_1577_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set_tag(v___x_1579_, 1);
lean_ctor_set(v___x_1579_, 0, v___x_1581_);
v___x_1583_ = v___x_1579_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg___boxed(lean_object* v_msg_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v_msg_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
return v_res_1592_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__0));
v___x_1595_ = l_Lean_stringToMessageData(v___x_1594_);
return v___x_1595_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__2));
v___x_1598_ = l_Lean_stringToMessageData(v___x_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(lean_object* v_t_1599_, lean_object* v_s_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
size_t v___x_1610_; size_t v___x_1611_; uint8_t v___x_1612_; 
v___x_1610_ = lean_ptr_addr(v_t_1599_);
v___x_1611_ = lean_ptr_addr(v_s_1600_);
v___x_1612_ = lean_usize_dec_eq(v___x_1610_, v___x_1611_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; 
lean_inc_ref(v_s_1600_);
lean_inc_ref(v_t_1599_);
v___x_1613_ = l_Lean_Meta_isExprDefEq(v_t_1599_, v_s_1600_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1631_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1631_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1631_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
uint8_t v___x_1618_; 
v___x_1618_ = lean_unbox(v_a_1614_);
lean_dec(v_a_1614_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
lean_del_object(v___x_1616_);
v___x_1619_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1);
v___x_1620_ = l_Lean_indentExpr(v_t_1599_);
v___x_1621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3);
v___x_1623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = l_Lean_indentExpr(v_s_1600_);
v___x_1625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1623_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v___x_1625_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
return v___x_1626_;
}
else
{
lean_object* v___x_1627_; lean_object* v___x_1629_; 
lean_dec_ref(v_s_1600_);
lean_dec_ref(v_t_1599_);
v___x_1627_ = lean_box(0);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v___x_1627_);
v___x_1629_ = v___x_1616_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec_ref(v_s_1600_);
lean_dec_ref(v_t_1599_);
v_a_1632_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1613_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1613_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_dec_ref(v_s_1600_);
lean_dec_ref(v_t_1599_);
v___x_1640_ = lean_box(0);
v___x_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
return v___x_1641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___boxed(lean_object* v_t_1642_, lean_object* v_s_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_t_1642_, v_s_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0(lean_object* v_00_u03b1_1654_, lean_object* v_msg_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v_msg_1655_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___boxed(lean_object* v_00_u03b1_1666_, lean_object* v_msg_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0(v_00_u03b1_1666_, v_msg_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
return v_res_1677_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__0));
v___x_1680_ = l_Lean_stringToMessageData(v___x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(lean_object* v_type_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
uint8_t v___x_1689_; 
v___x_1689_ = l_Lean_Expr_isForall(v_type_1681_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; 
lean_inc(v_a_1687_);
lean_inc_ref(v_a_1686_);
lean_inc(v_a_1685_);
lean_inc_ref(v_a_1684_);
v___x_1690_ = lean_whnf(v_type_1681_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; uint8_t v___x_1692_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref_known(v___x_1690_, 1);
v___x_1692_ = l_Lean_Expr_isForall(v_a_1691_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
v___x_1693_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1);
v___x_1694_ = l_Lean_indentExpr(v_a_1691_);
v___x_1695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1693_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v___x_1695_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1696_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1696_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
else
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_Meta_Sym_shareCommon(v_a_1691_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
return v___x_1705_;
}
}
else
{
return v___x_1690_;
}
}
else
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_type_1681_);
return v___x_1706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___boxed(lean_object* v_type_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_type_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall(lean_object* v_type_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_type_1716_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___boxed(lean_object* v_type_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall(v_type_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
lean_dec(v_a_1735_);
lean_dec_ref(v_a_1734_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
return v_res_1737_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_isClean(lean_object* v_e_1738_, lean_object* v_ctx_1739_){
_start:
{
lean_object* v_cleanSuffix_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; 
v_cleanSuffix_1740_ = lean_ctor_get(v_ctx_1739_, 2);
v___x_1741_ = l_Lean_Expr_looseBVarRange(v_e_1738_);
v___x_1742_ = lean_nat_dec_le(v___x_1741_, v_cleanSuffix_1740_);
lean_dec(v___x_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_isClean___boxed(lean_object* v_e_1743_, lean_object* v_ctx_1744_){
_start:
{
uint8_t v_res_1745_; lean_object* v_r_1746_; 
v_res_1745_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_isClean(v_e_1743_, v_ctx_1744_);
lean_dec_ref(v_ctx_1744_);
lean_dec_ref(v_e_1743_);
v_r_1746_ = lean_box(v_res_1745_);
return v_r_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(lean_object* v_e_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_e_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v_keyedConfig_1759_; uint8_t v_trackZetaDelta_1760_; lean_object* v_zetaDeltaSet_1761_; lean_object* v_lctx_1762_; lean_object* v_localInstances_1763_; lean_object* v_defEqCtx_x3f_1764_; lean_object* v_synthPendingDepth_1765_; lean_object* v_customCanUnfoldPredicate_x3f_1766_; uint8_t v_univApprox_1767_; uint8_t v_inTypeClassResolution_1768_; uint8_t v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref_known(v___x_1757_, 1);
v_keyedConfig_1759_ = lean_ctor_get(v_a_1752_, 0);
v_trackZetaDelta_1760_ = lean_ctor_get_uint8(v_a_1752_, sizeof(void*)*7);
v_zetaDeltaSet_1761_ = lean_ctor_get(v_a_1752_, 1);
v_lctx_1762_ = lean_ctor_get(v_a_1752_, 2);
v_localInstances_1763_ = lean_ctor_get(v_a_1752_, 3);
v_defEqCtx_x3f_1764_ = lean_ctor_get(v_a_1752_, 4);
v_synthPendingDepth_1765_ = lean_ctor_get(v_a_1752_, 5);
v_customCanUnfoldPredicate_x3f_1766_ = lean_ctor_get(v_a_1752_, 6);
v_univApprox_1767_ = lean_ctor_get_uint8(v_a_1752_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1768_ = lean_ctor_get_uint8(v_a_1752_, sizeof(void*)*7 + 2);
v___x_1769_ = 0;
lean_inc(v_customCanUnfoldPredicate_x3f_1766_);
lean_inc(v_synthPendingDepth_1765_);
lean_inc(v_defEqCtx_x3f_1764_);
lean_inc_ref(v_localInstances_1763_);
lean_inc_ref(v_lctx_1762_);
lean_inc(v_zetaDeltaSet_1761_);
lean_inc_ref(v_keyedConfig_1759_);
v___x_1770_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1770_, 0, v_keyedConfig_1759_);
lean_ctor_set(v___x_1770_, 1, v_zetaDeltaSet_1761_);
lean_ctor_set(v___x_1770_, 2, v_lctx_1762_);
lean_ctor_set(v___x_1770_, 3, v_localInstances_1763_);
lean_ctor_set(v___x_1770_, 4, v_defEqCtx_x3f_1764_);
lean_ctor_set(v___x_1770_, 5, v_synthPendingDepth_1765_);
lean_ctor_set(v___x_1770_, 6, v_customCanUnfoldPredicate_x3f_1766_);
lean_ctor_set_uint8(v___x_1770_, sizeof(void*)*7, v_trackZetaDelta_1760_);
lean_ctor_set_uint8(v___x_1770_, sizeof(void*)*7 + 1, v_univApprox_1767_);
lean_ctor_set_uint8(v___x_1770_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1768_);
lean_ctor_set_uint8(v___x_1770_, sizeof(void*)*7 + 3, v___x_1769_);
lean_inc(v_a_1755_);
lean_inc_ref(v_a_1754_);
lean_inc(v_a_1753_);
v___x_1771_ = lean_infer_type(v_a_1758_, v___x_1770_, v_a_1753_, v_a_1754_, v_a_1755_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1773_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
lean_dec_ref_known(v___x_1771_, 1);
v___x_1773_ = l_Lean_Meta_Sym_shareCommon(v_a_1772_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
return v___x_1773_;
}
else
{
return v___x_1771_;
}
}
else
{
return v___x_1757_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback___boxed(lean_object* v_e_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(v_e_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
lean_dec(v_a_1778_);
lean_dec_ref(v_a_1777_);
lean_dec(v_a_1776_);
lean_dec_ref(v_a_1775_);
return v_res_1784_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_instMonadEIO___redArg();
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(lean_object* v_msg_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v_toApplicative_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1867_; 
v___x_1800_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0);
v___x_1801_ = l_StateRefT_x27_instMonad___redArg(v___x_1800_);
v_toApplicative_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1867_ == 0)
{
lean_object* v_unused_1868_; 
v_unused_1868_ = lean_ctor_get(v___x_1801_, 1);
lean_dec(v_unused_1868_);
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1867_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_toApplicative_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1867_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v_toFunctor_1806_; lean_object* v_toSeq_1807_; lean_object* v_toSeqLeft_1808_; lean_object* v_toSeqRight_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1865_; 
v_toFunctor_1806_ = lean_ctor_get(v_toApplicative_1802_, 0);
v_toSeq_1807_ = lean_ctor_get(v_toApplicative_1802_, 2);
v_toSeqLeft_1808_ = lean_ctor_get(v_toApplicative_1802_, 3);
v_toSeqRight_1809_ = lean_ctor_get(v_toApplicative_1802_, 4);
v_isSharedCheck_1865_ = !lean_is_exclusive(v_toApplicative_1802_);
if (v_isSharedCheck_1865_ == 0)
{
lean_object* v_unused_1866_; 
v_unused_1866_ = lean_ctor_get(v_toApplicative_1802_, 1);
lean_dec(v_unused_1866_);
v___x_1811_ = v_toApplicative_1802_;
v_isShared_1812_ = v_isSharedCheck_1865_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_toSeqRight_1809_);
lean_inc(v_toSeqLeft_1808_);
lean_inc(v_toSeq_1807_);
lean_inc(v_toFunctor_1806_);
lean_dec(v_toApplicative_1802_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1865_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___f_1813_; lean_object* v___f_1814_; lean_object* v___f_1815_; lean_object* v___f_1816_; lean_object* v___x_1817_; lean_object* v___f_1818_; lean_object* v___f_1819_; lean_object* v___f_1820_; lean_object* v___x_1822_; 
v___f_1813_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__1));
v___f_1814_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1806_);
v___f_1815_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1815_, 0, v_toFunctor_1806_);
v___f_1816_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1816_, 0, v_toFunctor_1806_);
v___x_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___f_1815_);
lean_ctor_set(v___x_1817_, 1, v___f_1816_);
v___f_1818_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1818_, 0, v_toSeqRight_1809_);
v___f_1819_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1819_, 0, v_toSeqLeft_1808_);
v___f_1820_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1820_, 0, v_toSeq_1807_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 4, v___f_1818_);
lean_ctor_set(v___x_1811_, 3, v___f_1819_);
lean_ctor_set(v___x_1811_, 2, v___f_1820_);
lean_ctor_set(v___x_1811_, 1, v___f_1813_);
lean_ctor_set(v___x_1811_, 0, v___x_1817_);
v___x_1822_ = v___x_1811_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v___f_1813_);
lean_ctor_set(v_reuseFailAlloc_1864_, 2, v___f_1820_);
lean_ctor_set(v_reuseFailAlloc_1864_, 3, v___f_1819_);
lean_ctor_set(v_reuseFailAlloc_1864_, 4, v___f_1818_);
v___x_1822_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1824_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 1, v___f_1814_);
lean_ctor_set(v___x_1804_, 0, v___x_1822_);
v___x_1824_ = v___x_1804_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1822_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v___f_1814_);
v___x_1824_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1825_; lean_object* v_toApplicative_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1861_; 
v___x_1825_ = l_StateRefT_x27_instMonad___redArg(v___x_1824_);
v_toApplicative_1826_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1861_ == 0)
{
lean_object* v_unused_1862_; 
v_unused_1862_ = lean_ctor_get(v___x_1825_, 1);
lean_dec(v_unused_1862_);
v___x_1828_ = v___x_1825_;
v_isShared_1829_ = v_isSharedCheck_1861_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_toApplicative_1826_);
lean_dec(v___x_1825_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1861_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v_toFunctor_1830_; lean_object* v_toSeq_1831_; lean_object* v_toSeqLeft_1832_; lean_object* v_toSeqRight_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1859_; 
v_toFunctor_1830_ = lean_ctor_get(v_toApplicative_1826_, 0);
v_toSeq_1831_ = lean_ctor_get(v_toApplicative_1826_, 2);
v_toSeqLeft_1832_ = lean_ctor_get(v_toApplicative_1826_, 3);
v_toSeqRight_1833_ = lean_ctor_get(v_toApplicative_1826_, 4);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_toApplicative_1826_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; 
v_unused_1860_ = lean_ctor_get(v_toApplicative_1826_, 1);
lean_dec(v_unused_1860_);
v___x_1835_ = v_toApplicative_1826_;
v_isShared_1836_ = v_isSharedCheck_1859_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_toSeqRight_1833_);
lean_inc(v_toSeqLeft_1832_);
lean_inc(v_toSeq_1831_);
lean_inc(v_toFunctor_1830_);
lean_dec(v_toApplicative_1826_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1859_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___f_1837_; lean_object* v___f_1838_; lean_object* v___f_1839_; lean_object* v___f_1840_; lean_object* v___x_1841_; lean_object* v___f_1842_; lean_object* v___f_1843_; lean_object* v___f_1844_; lean_object* v___x_1846_; 
v___f_1837_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__3));
v___f_1838_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1830_);
v___f_1839_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1839_, 0, v_toFunctor_1830_);
v___f_1840_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1840_, 0, v_toFunctor_1830_);
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___f_1839_);
lean_ctor_set(v___x_1841_, 1, v___f_1840_);
v___f_1842_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1842_, 0, v_toSeqRight_1833_);
v___f_1843_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1843_, 0, v_toSeqLeft_1832_);
v___f_1844_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1844_, 0, v_toSeq_1831_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 4, v___f_1842_);
lean_ctor_set(v___x_1835_, 3, v___f_1843_);
lean_ctor_set(v___x_1835_, 2, v___f_1844_);
lean_ctor_set(v___x_1835_, 1, v___f_1837_);
lean_ctor_set(v___x_1835_, 0, v___x_1841_);
v___x_1846_ = v___x_1835_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1841_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v___f_1837_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v___f_1844_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v___f_1843_);
lean_ctor_set(v_reuseFailAlloc_1858_, 4, v___f_1842_);
v___x_1846_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1848_; 
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 1, v___f_1838_);
lean_ctor_set(v___x_1828_, 0, v___x_1846_);
v___x_1848_ = v___x_1828_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1846_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v___f_1838_);
v___x_1848_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___f_1854_; lean_object* v___x_11696__overap_1855_; lean_object* v___x_1856_; 
v___x_1849_ = l_StateRefT_x27_instMonad___redArg(v___x_1848_);
v___x_1850_ = l_ReaderT_instMonad___redArg(v___x_1849_);
v___x_1851_ = l_StateRefT_x27_instMonad___redArg(v___x_1850_);
v___x_1852_ = l_Lean_instInhabitedExpr;
v___x_1853_ = l_instInhabitedOfMonad___redArg(v___x_1851_, v___x_1852_);
v___f_1854_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1854_, 0, v___x_1853_);
v___x_11696__overap_1855_ = lean_panic_fn_borrowed(v___f_1854_, v_msg_1790_);
lean_dec_ref(v___f_1854_);
lean_inc(v___y_1798_);
lean_inc_ref(v___y_1797_);
lean_inc(v___y_1796_);
lean_inc_ref(v___y_1795_);
lean_inc(v___y_1794_);
lean_inc_ref(v___y_1793_);
lean_inc(v___y_1792_);
lean_inc_ref(v___y_1791_);
v___x_1856_ = lean_apply_9(v___x_11696__overap_1855_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, lean_box(0));
return v___x_1856_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___boxed(lean_object* v_msg_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(v_msg_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
return v_res_1879_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1882_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_1883_ = lean_unsigned_to_nat(44u);
v___x_1884_ = lean_unsigned_to_nat(367u);
v___x_1885_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__1));
v___x_1886_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0));
v___x_1887_ = l_mkPanicMessageWithDecl(v___x_1886_, v___x_1885_, v___x_1884_, v___x_1883_, v___x_1882_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(lean_object* v_e_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v_type_1899_; lean_object* v___y_1900_; uint8_t v___x_1918_; 
v___x_1918_ = l_Lean_Expr_hasLooseBVars(v_e_1888_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; 
v___x_1919_ = l_Lean_Meta_Sym_inferType(v_e_1888_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
return v___x_1919_;
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___y_1923_; lean_object* v_types_1927_; lean_object* v___x_1928_; 
v___x_1920_ = l_Lean_instInhabitedExpr;
v___x_1921_ = lean_st_ref_get(v_a_1890_);
v_types_1927_ = lean_ctor_get(v___x_1921_, 1);
lean_inc_ref(v_types_1927_);
lean_dec(v___x_1921_);
v___x_1928_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_types_1927_, v_e_1888_);
lean_dec_ref(v_types_1927_);
if (lean_obj_tag(v___x_1928_) == 1)
{
lean_object* v_val_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec_ref(v_e_1888_);
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
switch(lean_obj_tag(v_e_1888_))
{
case 0:
{
lean_object* v_xs_1937_; lean_object* v_deBruijnIndex_1938_; lean_object* v_size_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
v_xs_1937_ = lean_ctor_get(v_a_1889_, 0);
v_deBruijnIndex_1938_ = lean_ctor_get(v_e_1888_, 0);
v_size_1939_ = lean_ctor_get(v_xs_1937_, 2);
v___x_1940_ = lean_nat_sub(v_size_1939_, v_deBruijnIndex_1938_);
v___x_1941_ = lean_unsigned_to_nat(1u);
v___x_1942_ = lean_nat_sub(v___x_1940_, v___x_1941_);
lean_dec(v___x_1940_);
v___x_1943_ = lean_nat_dec_lt(v___x_1942_, v_size_1939_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; 
lean_dec(v___x_1942_);
v___x_1944_ = l_outOfBounds___redArg(v___x_1920_);
v___y_1923_ = v___x_1944_;
goto v___jp_1922_;
}
else
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1920_, v_xs_1937_, v___x_1942_);
lean_dec(v___x_1942_);
v___y_1923_ = v___x_1945_;
goto v___jp_1922_;
}
}
case 10:
{
lean_object* v_expr_1946_; lean_object* v___x_1947_; 
v_expr_1946_ = lean_ctor_get(v_e_1888_, 1);
lean_inc_ref(v_expr_1946_);
v___x_1947_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_expr_1946_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___x_1947_, 1);
v_type_1899_ = v_a_1948_;
v___y_1900_ = v_a_1890_;
goto v___jp_1898_;
}
else
{
lean_dec_ref_known(v_e_1888_, 2);
return v___x_1947_;
}
}
case 5:
{
lean_object* v_fn_1949_; lean_object* v_arg_1950_; lean_object* v___x_1951_; 
v_fn_1949_ = lean_ctor_get(v_e_1888_, 0);
v_arg_1950_ = lean_ctor_get(v_e_1888_, 1);
lean_inc_ref(v_fn_1949_);
v___x_1951_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_fn_1949_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1953_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
v___x_1953_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_a_1952_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref_known(v___x_1953_, 1);
if (lean_obj_tag(v_a_1954_) == 7)
{
lean_object* v_body_1955_; uint8_t v___x_1956_; 
v_body_1955_ = lean_ctor_get(v_a_1954_, 2);
lean_inc_ref(v_body_1955_);
lean_dec_ref_known(v_a_1954_, 3);
v___x_1956_ = l_Lean_Expr_hasLooseBVars(v_body_1955_);
if (v___x_1956_ == 0)
{
v_type_1899_ = v_body_1955_;
v___y_1900_ = v_a_1890_;
goto v___jp_1898_;
}
else
{
lean_object* v___x_1957_; 
lean_inc_ref(v_arg_1950_);
v___x_1957_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_arg_1950_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v___x_1959_ = lean_expr_instantiate1(v_body_1955_, v_a_1958_);
lean_dec(v_a_1958_);
lean_dec_ref(v_body_1955_);
v___x_1960_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1959_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref_known(v___x_1960_, 1);
v_type_1899_ = v_a_1961_;
v___y_1900_ = v_a_1890_;
goto v___jp_1898_;
}
else
{
lean_dec_ref_known(v_e_1888_, 2);
return v___x_1960_;
}
}
else
{
lean_dec_ref(v_body_1955_);
lean_dec_ref_known(v_e_1888_, 2);
return v___x_1957_;
}
}
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
lean_dec(v_a_1954_);
v___x_1962_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2);
v___x_1963_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(v___x_1962_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_1964_);
lean_dec_ref_known(v___x_1963_, 1);
v_type_1899_ = v_a_1964_;
v___y_1900_ = v_a_1890_;
goto v___jp_1898_;
}
else
{
lean_dec_ref_known(v_e_1888_, 2);
return v___x_1963_;
}
}
}
else
{
lean_dec_ref_known(v_e_1888_, 2);
return v___x_1953_;
}
}
else
{
lean_dec_ref_known(v_e_1888_, 2);
return v___x_1951_;
}
}
default: 
{
lean_object* v___x_1965_; 
lean_inc_ref(v_e_1888_);
v___x_1965_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(v_e_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref_known(v___x_1965_, 1);
v_type_1899_ = v_a_1966_;
v___y_1900_ = v_a_1890_;
goto v___jp_1898_;
}
else
{
lean_dec_ref(v_e_1888_);
return v___x_1965_;
}
}
}
}
v___jp_1922_:
{
lean_object* v_lctx_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_lctx_1924_ = lean_ctor_get(v_a_1893_, 2);
lean_inc_ref(v_lctx_1924_);
v___x_1925_ = l_Lean_LocalContext_getFVar_x21(v_lctx_1924_, v___y_1923_);
lean_dec_ref(v___y_1923_);
v___x_1926_ = l_Lean_LocalDecl_type(v___x_1925_);
lean_dec_ref(v___x_1925_);
v_type_1899_ = v___x_1926_;
v___y_1900_ = v_a_1890_;
goto v___jp_1898_;
}
}
v___jp_1898_:
{
lean_object* v___x_1901_; lean_object* v_visited_1902_; lean_object* v_types_1903_; lean_object* v_subst_1904_; lean_object* v_visitedClosed_1905_; lean_object* v_hasDepLetCache_1906_; lean_object* v_numConverted_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1917_; 
v___x_1901_ = lean_st_ref_take(v___y_1900_);
v_visited_1902_ = lean_ctor_get(v___x_1901_, 0);
v_types_1903_ = lean_ctor_get(v___x_1901_, 1);
v_subst_1904_ = lean_ctor_get(v___x_1901_, 2);
v_visitedClosed_1905_ = lean_ctor_get(v___x_1901_, 3);
v_hasDepLetCache_1906_ = lean_ctor_get(v___x_1901_, 4);
v_numConverted_1907_ = lean_ctor_get(v___x_1901_, 5);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1909_ = v___x_1901_;
v_isShared_1910_ = v_isSharedCheck_1917_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_numConverted_1907_);
lean_inc(v_hasDepLetCache_1906_);
lean_inc(v_visitedClosed_1905_);
lean_inc(v_subst_1904_);
lean_inc(v_types_1903_);
lean_inc(v_visited_1902_);
lean_dec(v___x_1901_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1917_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1911_; lean_object* v___x_1913_; 
lean_inc_ref(v_type_1899_);
v___x_1911_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_types_1903_, v_e_1888_, v_type_1899_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 1, v___x_1911_);
v___x_1913_ = v___x_1909_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_visited_1902_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v___x_1911_);
lean_ctor_set(v_reuseFailAlloc_1916_, 2, v_subst_1904_);
lean_ctor_set(v_reuseFailAlloc_1916_, 3, v_visitedClosed_1905_);
lean_ctor_set(v_reuseFailAlloc_1916_, 4, v_hasDepLetCache_1906_);
lean_ctor_set(v_reuseFailAlloc_1916_, 5, v_numConverted_1907_);
v___x_1913_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_st_ref_put(v___y_1900_, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v_type_1899_);
return v___x_1915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___boxed(lean_object* v_e_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_e_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1974_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(lean_object* v_fvarId_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = l_Lean_Expr_fvar___override(v_fvarId_1978_);
v___x_1982_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1981_, v___y_1979_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg___boxed(lean_object* v_fvarId_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(v_fvarId_1983_, v___y_1984_);
lean_dec(v___y_1984_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1(lean_object* v_fvarId_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(v_fvarId_1987_, v___y_1991_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___boxed(lean_object* v_fvarId_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1(v_fvarId_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0(lean_object* v_x_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v___x_2019_; 
lean_inc(v___y_2013_);
lean_inc_ref(v___y_2012_);
lean_inc(v___y_2011_);
lean_inc_ref(v___y_2010_);
v___x_2019_ = lean_apply_9(v_x_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, lean_box(0));
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0___boxed(lean_object* v_x_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0(v_x_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(lean_object* v_lctx_2031_, lean_object* v_localInsts_2032_, lean_object* v_x_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v___f_2043_; lean_object* v___x_2044_; 
lean_inc(v___y_2037_);
lean_inc_ref(v___y_2036_);
lean_inc(v___y_2035_);
lean_inc_ref(v___y_2034_);
v___f_2043_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2043_, 0, v_x_2033_);
lean_closure_set(v___f_2043_, 1, v___y_2034_);
lean_closure_set(v___f_2043_, 2, v___y_2035_);
lean_closure_set(v___f_2043_, 3, v___y_2036_);
lean_closure_set(v___f_2043_, 4, v___y_2037_);
v___x_2044_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2031_, v_localInsts_2032_, v___f_2043_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2044_) == 0)
{
return v___x_2044_;
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2044_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2044_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___boxed(lean_object* v_lctx_2053_, lean_object* v_localInsts_2054_, lean_object* v_x_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(v_lctx_2053_, v_localInsts_2054_, v_x_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2(lean_object* v_00_u03b1_2066_, lean_object* v_lctx_2067_, lean_object* v_localInsts_2068_, lean_object* v_x_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v___x_2079_; 
v___x_2079_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(v_lctx_2067_, v_localInsts_2068_, v_x_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___boxed(lean_object* v_00_u03b1_2080_, lean_object* v_lctx_2081_, lean_object* v_localInsts_2082_, lean_object* v_x_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2(v_00_u03b1_2080_, v_lctx_2081_, v_localInsts_2082_, v_x_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(lean_object* v___y_2094_, lean_object* v_visited_2095_, lean_object* v_types_2096_, lean_object* v_subst_2097_, lean_object* v_a_x3f_2098_){
_start:
{
lean_object* v___x_2100_; lean_object* v_visitedClosed_2101_; lean_object* v_hasDepLetCache_2102_; lean_object* v_numConverted_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2113_; 
v___x_2100_ = lean_st_ref_take(v___y_2094_);
v_visitedClosed_2101_ = lean_ctor_get(v___x_2100_, 3);
v_hasDepLetCache_2102_ = lean_ctor_get(v___x_2100_, 4);
v_numConverted_2103_ = lean_ctor_get(v___x_2100_, 5);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2113_ == 0)
{
lean_object* v_unused_2114_; lean_object* v_unused_2115_; lean_object* v_unused_2116_; 
v_unused_2114_ = lean_ctor_get(v___x_2100_, 2);
lean_dec(v_unused_2114_);
v_unused_2115_ = lean_ctor_get(v___x_2100_, 1);
lean_dec(v_unused_2115_);
v_unused_2116_ = lean_ctor_get(v___x_2100_, 0);
lean_dec(v_unused_2116_);
v___x_2105_ = v___x_2100_;
v_isShared_2106_ = v_isSharedCheck_2113_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_numConverted_2103_);
lean_inc(v_hasDepLetCache_2102_);
lean_inc(v_visitedClosed_2101_);
lean_dec(v___x_2100_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2113_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2107_ = lean_box(0);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 2, v_subst_2097_);
lean_ctor_set(v___x_2105_, 1, v_types_2096_);
lean_ctor_set(v___x_2105_, 0, v_visited_2095_);
v___x_2109_ = v___x_2105_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_visited_2095_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_types_2096_);
lean_ctor_set(v_reuseFailAlloc_2112_, 2, v_subst_2097_);
lean_ctor_set(v_reuseFailAlloc_2112_, 3, v_visitedClosed_2101_);
lean_ctor_set(v_reuseFailAlloc_2112_, 4, v_hasDepLetCache_2102_);
lean_ctor_set(v_reuseFailAlloc_2112_, 5, v_numConverted_2103_);
v___x_2109_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = lean_st_ref_put(v___y_2094_, v___x_2109_);
v___x_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2107_);
return v___x_2111_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0___boxed(lean_object* v___y_2117_, lean_object* v_visited_2118_, lean_object* v_types_2119_, lean_object* v_subst_2120_, lean_object* v_a_x3f_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(v___y_2117_, v_visited_2118_, v_types_2119_, v_subst_2120_, v_a_x3f_2121_);
lean_dec(v_a_x3f_2121_);
lean_dec(v___y_2117_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1(lean_object* v_k_2124_, lean_object* v_a_2125_, uint8_t v_tainted_2126_, uint8_t v_isCandidate_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v___y_2138_; lean_object* v_xs_2184_; lean_object* v_numCandidates_2185_; lean_object* v_cleanSuffix_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2205_; 
v_xs_2184_ = lean_ctor_get(v___y_2128_, 0);
v_numCandidates_2185_ = lean_ctor_get(v___y_2128_, 1);
v_cleanSuffix_2186_ = lean_ctor_get(v___y_2128_, 2);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___y_2128_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2188_ = v___y_2128_;
v_isShared_2189_ = v_isSharedCheck_2205_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_cleanSuffix_2186_);
lean_inc(v_numCandidates_2185_);
lean_inc(v_xs_2184_);
lean_dec(v___y_2128_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2205_;
goto v_resetjp_2187_;
}
v___jp_2137_:
{
lean_object* v___x_2139_; lean_object* v_visited_2140_; lean_object* v_types_2141_; lean_object* v_subst_2142_; lean_object* v_visitedClosed_2143_; lean_object* v_hasDepLetCache_2144_; lean_object* v_numConverted_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2183_; 
v___x_2139_ = lean_st_ref_take(v___y_2129_);
v_visited_2140_ = lean_ctor_get(v___x_2139_, 0);
v_types_2141_ = lean_ctor_get(v___x_2139_, 1);
v_subst_2142_ = lean_ctor_get(v___x_2139_, 2);
v_visitedClosed_2143_ = lean_ctor_get(v___x_2139_, 3);
v_hasDepLetCache_2144_ = lean_ctor_get(v___x_2139_, 4);
v_numConverted_2145_ = lean_ctor_get(v___x_2139_, 5);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2147_ = v___x_2139_;
v_isShared_2148_ = v_isSharedCheck_2183_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_numConverted_2145_);
lean_inc(v_hasDepLetCache_2144_);
lean_inc(v_visitedClosed_2143_);
lean_inc(v_subst_2142_);
lean_inc(v_types_2141_);
lean_inc(v_visited_2140_);
lean_dec(v___x_2139_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2183_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2149_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 2, v___x_2149_);
lean_ctor_set(v___x_2147_, 1, v___x_2149_);
lean_ctor_set(v___x_2147_, 0, v___x_2149_);
v___x_2151_ = v___x_2147_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2182_, 2, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2182_, 3, v_visitedClosed_2143_);
lean_ctor_set(v_reuseFailAlloc_2182_, 4, v_hasDepLetCache_2144_);
lean_ctor_set(v_reuseFailAlloc_2182_, 5, v_numConverted_2145_);
v___x_2151_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2152_; lean_object* v_r_2153_; 
v___x_2152_ = lean_st_ref_put(v___y_2129_, v___x_2151_);
lean_inc(v___y_2135_);
lean_inc_ref(v___y_2134_);
lean_inc(v___y_2133_);
lean_inc_ref(v___y_2132_);
lean_inc(v___y_2131_);
lean_inc_ref(v___y_2130_);
lean_inc(v___y_2129_);
v_r_2153_ = lean_apply_10(v_k_2124_, v_a_2125_, v___y_2138_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, lean_box(0));
if (lean_obj_tag(v_r_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2170_; 
v_a_2154_ = lean_ctor_get(v_r_2153_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_r_2153_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2156_ = v_r_2153_;
v_isShared_2157_ = v_isSharedCheck_2170_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v_r_2153_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2170_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
lean_inc(v_a_2154_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set_tag(v___x_2156_, 1);
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
v___x_2160_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(v___y_2129_, v_visited_2140_, v_types_2141_, v_subst_2142_, v___x_2159_);
lean_dec_ref(v___x_2159_);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2167_ == 0)
{
lean_object* v_unused_2168_; 
v_unused_2168_ = lean_ctor_get(v___x_2160_, 0);
lean_dec(v_unused_2168_);
v___x_2162_ = v___x_2160_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_dec(v___x_2160_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v_a_2154_);
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2154_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
v_a_2171_ = lean_ctor_get(v_r_2153_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v_r_2153_, 1);
v___x_2172_ = lean_box(0);
v___x_2173_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(v___y_2129_, v_visited_2140_, v_types_2141_, v_subst_2142_, v___x_2172_);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2180_ == 0)
{
lean_object* v_unused_2181_; 
v_unused_2181_ = lean_ctor_get(v___x_2173_, 0);
lean_dec(v_unused_2181_);
v___x_2175_ = v___x_2173_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_dec(v___x_2173_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
lean_ctor_set_tag(v___x_2175_, 1);
lean_ctor_set(v___x_2175_, 0, v_a_2171_);
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2171_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
}
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; lean_object* v___y_2192_; 
lean_inc_ref(v_a_2125_);
v___x_2190_ = l_Lean_PersistentArray_push___redArg(v_xs_2184_, v_a_2125_);
if (v_isCandidate_2127_ == 0)
{
lean_object* v___x_2203_; 
v___x_2203_ = lean_unsigned_to_nat(0u);
v___y_2192_ = v___x_2203_;
goto v___jp_2191_;
}
else
{
lean_object* v___x_2204_; 
v___x_2204_ = lean_unsigned_to_nat(1u);
v___y_2192_ = v___x_2204_;
goto v___jp_2191_;
}
v___jp_2191_:
{
lean_object* v___x_2193_; 
v___x_2193_ = lean_nat_add(v_numCandidates_2185_, v___y_2192_);
lean_dec(v_numCandidates_2185_);
if (v_tainted_2126_ == 0)
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2194_ = lean_unsigned_to_nat(1u);
v___x_2195_ = lean_nat_add(v_cleanSuffix_2186_, v___x_2194_);
lean_dec(v_cleanSuffix_2186_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 2, v___x_2195_);
lean_ctor_set(v___x_2188_, 1, v___x_2193_);
lean_ctor_set(v___x_2188_, 0, v___x_2190_);
v___x_2197_ = v___x_2188_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v___x_2193_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
v___y_2138_ = v___x_2197_;
goto v___jp_2137_;
}
}
else
{
lean_object* v___x_2199_; lean_object* v___x_2201_; 
lean_dec(v_cleanSuffix_2186_);
v___x_2199_ = lean_unsigned_to_nat(0u);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 2, v___x_2199_);
lean_ctor_set(v___x_2188_, 1, v___x_2193_);
lean_ctor_set(v___x_2188_, 0, v___x_2190_);
v___x_2201_ = v___x_2188_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v___x_2193_);
lean_ctor_set(v_reuseFailAlloc_2202_, 2, v___x_2199_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
v___y_2138_ = v___x_2201_;
goto v___jp_2137_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1___boxed(lean_object* v_k_2206_, lean_object* v_a_2207_, lean_object* v_tainted_2208_, lean_object* v_isCandidate_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
uint8_t v_tainted_boxed_2219_; uint8_t v_isCandidate_boxed_2220_; lean_object* v_res_2221_; 
v_tainted_boxed_2219_ = lean_unbox(v_tainted_2208_);
v_isCandidate_boxed_2220_ = lean_unbox(v_isCandidate_2209_);
v_res_2221_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1(v_k_2206_, v_a_2207_, v_tainted_boxed_2219_, v_isCandidate_boxed_2220_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg(lean_object* v___y_2222_){
_start:
{
lean_object* v___x_2224_; lean_object* v_ngen_2225_; lean_object* v_namePrefix_2226_; lean_object* v_idx_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2257_; 
v___x_2224_ = lean_st_ref_get(v___y_2222_);
v_ngen_2225_ = lean_ctor_get(v___x_2224_, 2);
lean_inc_ref(v_ngen_2225_);
lean_dec(v___x_2224_);
v_namePrefix_2226_ = lean_ctor_get(v_ngen_2225_, 0);
v_idx_2227_ = lean_ctor_get(v_ngen_2225_, 1);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_ngen_2225_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2229_ = v_ngen_2225_;
v_isShared_2230_ = v_isSharedCheck_2257_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_idx_2227_);
lean_inc(v_namePrefix_2226_);
lean_dec(v_ngen_2225_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2257_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v_r_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2235_; 
lean_inc(v_idx_2227_);
lean_inc(v_namePrefix_2226_);
v_r_2231_ = l_Lean_Name_num___override(v_namePrefix_2226_, v_idx_2227_);
v___x_2232_ = lean_unsigned_to_nat(1u);
v___x_2233_ = lean_nat_add(v_idx_2227_, v___x_2232_);
lean_dec(v_idx_2227_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 1, v___x_2233_);
v___x_2235_ = v___x_2229_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_namePrefix_2226_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2236_; lean_object* v_env_2237_; lean_object* v_nextMacroScope_2238_; lean_object* v_auxDeclNGen_2239_; lean_object* v_traceState_2240_; lean_object* v_cache_2241_; lean_object* v_recordedDeps_2242_; lean_object* v_messages_2243_; lean_object* v_infoState_2244_; lean_object* v_snapshotTasks_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2254_; 
v___x_2236_ = lean_st_ref_take(v___y_2222_);
v_env_2237_ = lean_ctor_get(v___x_2236_, 0);
v_nextMacroScope_2238_ = lean_ctor_get(v___x_2236_, 1);
v_auxDeclNGen_2239_ = lean_ctor_get(v___x_2236_, 3);
v_traceState_2240_ = lean_ctor_get(v___x_2236_, 4);
v_cache_2241_ = lean_ctor_get(v___x_2236_, 5);
v_recordedDeps_2242_ = lean_ctor_get(v___x_2236_, 6);
v_messages_2243_ = lean_ctor_get(v___x_2236_, 7);
v_infoState_2244_ = lean_ctor_get(v___x_2236_, 8);
v_snapshotTasks_2245_ = lean_ctor_get(v___x_2236_, 9);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2254_ == 0)
{
lean_object* v_unused_2255_; 
v_unused_2255_ = lean_ctor_get(v___x_2236_, 2);
lean_dec(v_unused_2255_);
v___x_2247_ = v___x_2236_;
v_isShared_2248_ = v_isSharedCheck_2254_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_snapshotTasks_2245_);
lean_inc(v_infoState_2244_);
lean_inc(v_messages_2243_);
lean_inc(v_recordedDeps_2242_);
lean_inc(v_cache_2241_);
lean_inc(v_traceState_2240_);
lean_inc(v_auxDeclNGen_2239_);
lean_inc(v_nextMacroScope_2238_);
lean_inc(v_env_2237_);
lean_dec(v___x_2236_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2254_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 2, v___x_2235_);
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_env_2237_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_nextMacroScope_2238_);
lean_ctor_set(v_reuseFailAlloc_2253_, 2, v___x_2235_);
lean_ctor_set(v_reuseFailAlloc_2253_, 3, v_auxDeclNGen_2239_);
lean_ctor_set(v_reuseFailAlloc_2253_, 4, v_traceState_2240_);
lean_ctor_set(v_reuseFailAlloc_2253_, 5, v_cache_2241_);
lean_ctor_set(v_reuseFailAlloc_2253_, 6, v_recordedDeps_2242_);
lean_ctor_set(v_reuseFailAlloc_2253_, 7, v_messages_2243_);
lean_ctor_set(v_reuseFailAlloc_2253_, 8, v_infoState_2244_);
lean_ctor_set(v_reuseFailAlloc_2253_, 9, v_snapshotTasks_2245_);
v___x_2250_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = lean_st_ref_put(v___y_2222_, v___x_2250_);
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v_r_2231_);
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
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___f_2481_; lean_object* v___x_5629__overap_2482_; lean_object* v___x_2483_; 
v___x_2476_ = l_StateRefT_x27_instMonad___redArg(v___x_2475_);
v___x_2477_ = l_ReaderT_instMonad___redArg(v___x_2476_);
v___x_2478_ = l_StateRefT_x27_instMonad___redArg(v___x_2477_);
v___x_2479_ = lean_box(0);
v___x_2480_ = l_instInhabitedOfMonad___redArg(v___x_2478_, v___x_2479_);
v___f_2481_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2481_, 0, v___x_2480_);
v___x_5629__overap_2482_ = lean_panic_fn_borrowed(v___f_2481_, v_msg_2417_);
lean_dec_ref(v___f_2481_);
lean_inc(v___y_2425_);
lean_inc_ref(v___y_2424_);
lean_inc(v___y_2423_);
lean_inc_ref(v___y_2422_);
lean_inc(v___y_2421_);
lean_inc_ref(v___y_2420_);
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
v___x_2483_ = lean_apply_9(v___x_5629__overap_2482_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, lean_box(0));
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
lean_object* v_binderType_2543_; lean_object* v_body_2544_; lean_object* v___f_2545_; lean_object* v___x_2546_; 
v_binderType_2543_ = lean_ctor_get(v_a_2542_, 1);
lean_inc_ref(v_binderType_2543_);
v_body_2544_ = lean_ctor_get(v_a_2542_, 2);
lean_inc_ref(v_body_2544_);
lean_dec_ref_known(v_a_2542_, 3);
v___f_2545_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0___boxed), 12, 2);
lean_closure_set(v___f_2545_, 0, v_body_2544_);
lean_closure_set(v___f_2545_, 1, v_body_2540_);
lean_inc_ref(v_binderType_2539_);
v___x_2546_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_binderType_2539_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2548_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc_n(v_a_2547_, 2);
lean_dec_ref_known(v___x_2546_, 1);
v___x_2548_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_a_2547_, v_binderType_2543_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_cleanSuffix_2549_; lean_object* v___x_2550_; uint8_t v___y_2552_; lean_object* v___x_2555_; uint8_t v___x_2556_; 
lean_dec_ref_known(v___x_2548_, 1);
v_cleanSuffix_2549_ = lean_ctor_get(v_a_2529_, 2);
v___x_2550_ = lean_box(0);
v___x_2555_ = l_Lean_Expr_looseBVarRange(v_binderType_2539_);
lean_dec_ref(v_binderType_2539_);
v___x_2556_ = lean_nat_dec_le(v___x_2555_, v_cleanSuffix_2549_);
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
v___x_2554_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_binderName_2538_, v_a_2547_, v___x_2550_, v___y_2552_, v___x_2553_, v___f_2545_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
return v___x_2554_;
}
}
else
{
lean_dec(v_a_2547_);
lean_dec_ref(v___f_2545_);
lean_dec_ref(v_binderType_2539_);
lean_dec(v_binderName_2538_);
return v___x_2548_;
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec_ref(v___f_2545_);
lean_dec_ref(v_binderType_2543_);
lean_dec_ref(v_binderType_2539_);
lean_dec(v_binderName_2538_);
v_a_2559_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2546_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2546_);
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
lean_object* v_numCandidates_2637_; lean_object* v_cleanSuffix_2638_; lean_object* v___x_2639_; uint8_t v___x_2640_; 
v_numCandidates_2637_ = lean_ctor_get(v_a_2628_, 1);
v_cleanSuffix_2638_ = lean_ctor_get(v_a_2628_, 2);
v___x_2639_ = lean_unsigned_to_nat(0u);
v___x_2640_ = lean_nat_dec_lt(v___x_2639_, v_numCandidates_2637_);
if (v___x_2640_ == 0)
{
lean_dec_ref(v_tf_2627_);
goto v___jp_2634_;
}
else
{
lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2641_ = l_Lean_Expr_looseBVarRange(v_t_2626_);
v___x_2642_ = lean_nat_dec_le(v___x_2641_, v_cleanSuffix_2638_);
lean_dec(v___x_2641_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = lean_box(0);
v___x_2644_ = l_Lean_Meta_getLevel(v_tf_2627_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2651_ == 0)
{
lean_object* v_unused_2652_; 
v_unused_2652_ = lean_ctor_get(v___x_2644_, 0);
lean_dec(v_unused_2652_);
v___x_2646_ = v___x_2644_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_dec(v___x_2644_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v___x_2643_);
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2643_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
v_a_2653_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2644_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2644_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg___boxed(lean_object* v_t_2661_, lean_object* v_tf_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_t_2661_, v_tf_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec_ref(v_t_2661_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain(lean_object* v_t_2670_, lean_object* v_tf_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_t_2670_, v_tf_2671_, v_a_2672_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___boxed(lean_object* v_t_2682_, lean_object* v_tf_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain(v_t_2682_, v_tf_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
lean_dec_ref(v_t_2682_);
return v_res_2693_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1(void){
_start:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2695_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_2696_ = lean_unsigned_to_nat(35u);
v___x_2697_ = lean_unsigned_to_nat(322u);
v___x_2698_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__0));
v___x_2699_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0));
v___x_2700_ = l_mkPanicMessageWithDecl(v___x_2699_, v___x_2698_, v___x_2697_, v___x_2696_, v___x_2695_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp(lean_object* v_f_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_f_2701_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v___x_2714_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
lean_inc(v_a_2713_);
lean_dec_ref_known(v___x_2712_, 1);
v___x_2714_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_a_2713_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2742_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2717_ = v___x_2714_;
v_isShared_2718_ = v_isSharedCheck_2742_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2714_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2742_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
if (lean_obj_tag(v_a_2715_) == 7)
{
lean_object* v_binderType_2719_; uint8_t v___x_2734_; 
v_binderType_2719_ = lean_ctor_get(v_a_2715_, 1);
lean_inc_ref(v_binderType_2719_);
lean_dec_ref_known(v_a_2715_, 3);
v___x_2734_ = l_Lean_Expr_hasLooseBVars(v_a_2702_);
if (v___x_2734_ == 0)
{
uint8_t v___x_2735_; 
v___x_2735_ = l_Lean_Expr_hasFVar(v_binderType_2719_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; lean_object* v___x_2738_; 
lean_dec_ref(v_binderType_2719_);
lean_dec_ref(v_a_2702_);
v___x_2736_ = lean_box(0);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 0, v___x_2736_);
v___x_2738_ = v___x_2717_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2736_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
else
{
lean_del_object(v___x_2717_);
goto v___jp_2720_;
}
}
else
{
lean_del_object(v___x_2717_);
goto v___jp_2720_;
}
v___jp_2720_:
{
uint8_t v___x_2721_; 
v___x_2721_ = l_Lean_Expr_isLambda(v_a_2702_);
if (v___x_2721_ == 0)
{
lean_object* v___x_2722_; 
v___x_2722_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; lean_object* v___x_2724_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
lean_inc(v_a_2723_);
lean_dec_ref_known(v___x_2722_, 1);
v___x_2724_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_a_2723_, v_binderType_2719_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
return v___x_2724_;
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec_ref(v_binderType_2719_);
v_a_2725_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2722_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2722_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
else
{
lean_object* v___x_2733_; 
v___x_2733_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_a_2702_, v_binderType_2719_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
return v___x_2733_;
}
}
}
else
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
lean_del_object(v___x_2717_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2702_);
v___x_2740_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1);
v___x_2741_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0(v___x_2740_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
return v___x_2741_;
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec_ref(v_a_2702_);
v_a_2743_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2714_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2714_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec_ref(v_a_2702_);
v_a_2751_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2712_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2712_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___boxed(lean_object* v_f_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp(v_f_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_);
lean_dec(v_a_2768_);
lean_dec_ref(v_a_2767_);
lean_dec(v_a_2766_);
lean_dec_ref(v_a_2765_);
lean_dec(v_a_2764_);
lean_dec_ref(v_a_2763_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2761_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(lean_object* v_x_2771_, uint8_t v_bi_2772_, lean_object* v_t_2773_, lean_object* v_b_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v___y_2783_; lean_object* v___x_2786_; uint8_t v_debug_2787_; 
v___x_2786_ = lean_st_ref_get(v___y_2776_);
v_debug_2787_ = lean_ctor_get_uint8(v___x_2786_, sizeof(void*)*11);
lean_dec(v___x_2786_);
if (v_debug_2787_ == 0)
{
v___y_2783_ = v___y_2776_;
goto v___jp_2782_;
}
else
{
lean_object* v___x_2788_; 
v___x_2788_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2773_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v___x_2789_; 
lean_dec_ref_known(v___x_2788_, 1);
v___x_2789_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_dec_ref_known(v___x_2789_, 1);
v___y_2783_ = v___y_2776_;
goto v___jp_2782_;
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
lean_dec_ref(v_b_2774_);
lean_dec_ref(v_t_2773_);
lean_dec(v_x_2771_);
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2792_ = v___x_2789_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2789_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
else
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2805_; 
lean_dec_ref(v_b_2774_);
lean_dec_ref(v_t_2773_);
lean_dec(v_x_2771_);
v_a_2798_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2800_ = v___x_2788_;
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2788_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
v___jp_2782_:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = l_Lean_Expr_lam___override(v_x_2771_, v_t_2773_, v_b_2774_, v_bi_2772_);
v___x_2785_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2784_, v___y_2783_);
return v___x_2785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg___boxed(lean_object* v_x_2806_, lean_object* v_bi_2807_, lean_object* v_t_2808_, lean_object* v_b_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
uint8_t v_bi_boxed_2817_; lean_object* v_res_2818_; 
v_bi_boxed_2817_ = lean_unbox(v_bi_2807_);
v_res_2818_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(v_x_2806_, v_bi_boxed_2817_, v_t_2808_, v_b_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(lean_object* v_x_2819_, lean_object* v_t_2820_, lean_object* v_v_2821_, lean_object* v_b_2822_, uint8_t v_nondep_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v___y_2832_; lean_object* v___x_2835_; uint8_t v_debug_2836_; 
v___x_2835_ = lean_st_ref_get(v___y_2825_);
v_debug_2836_ = lean_ctor_get_uint8(v___x_2835_, sizeof(void*)*11);
lean_dec(v___x_2835_);
if (v_debug_2836_ == 0)
{
v___y_2832_ = v___y_2825_;
goto v___jp_2831_;
}
else
{
lean_object* v___x_2837_; 
v___x_2837_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2820_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v___x_2838_; 
lean_dec_ref_known(v___x_2837_, 1);
v___x_2838_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_v_2821_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v___x_2839_; 
lean_dec_ref_known(v___x_2838_, 1);
v___x_2839_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2822_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_dec_ref_known(v___x_2839_, 1);
v___y_2832_ = v___y_2825_;
goto v___jp_2831_;
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec_ref(v_b_2822_);
lean_dec_ref(v_v_2821_);
lean_dec_ref(v_t_2820_);
lean_dec(v_x_2819_);
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec_ref(v_b_2822_);
lean_dec_ref(v_v_2821_);
lean_dec_ref(v_t_2820_);
lean_dec(v_x_2819_);
v_a_2848_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2838_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2838_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_dec_ref(v_b_2822_);
lean_dec_ref(v_v_2821_);
lean_dec_ref(v_t_2820_);
lean_dec(v_x_2819_);
v_a_2856_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2837_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2837_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
v___jp_2831_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = l_Lean_Expr_letE___override(v_x_2819_, v_t_2820_, v_v_2821_, v_b_2822_, v_nondep_2823_);
v___x_2834_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2833_, v___y_2832_);
return v___x_2834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg___boxed(lean_object* v_x_2864_, lean_object* v_t_2865_, lean_object* v_v_2866_, lean_object* v_b_2867_, lean_object* v_nondep_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
uint8_t v_nondep_boxed_2876_; lean_object* v_res_2877_; 
v_nondep_boxed_2876_ = lean_unbox(v_nondep_2868_);
v_res_2877_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_x_2864_, v_t_2865_, v_v_2866_, v_b_2867_, v_nondep_boxed_2876_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
return v_res_2877_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(lean_object* v_k_2878_, lean_object* v_t_2879_){
_start:
{
if (lean_obj_tag(v_t_2879_) == 0)
{
lean_object* v_k_2880_; lean_object* v_l_2881_; lean_object* v_r_2882_; uint8_t v___x_2883_; 
v_k_2880_ = lean_ctor_get(v_t_2879_, 1);
v_l_2881_ = lean_ctor_get(v_t_2879_, 3);
v_r_2882_ = lean_ctor_get(v_t_2879_, 4);
v___x_2883_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2878_, v_k_2880_);
switch(v___x_2883_)
{
case 0:
{
v_t_2879_ = v_l_2881_;
goto _start;
}
case 1:
{
uint8_t v___x_2885_; 
v___x_2885_ = 1;
return v___x_2885_;
}
default: 
{
v_t_2879_ = v_r_2882_;
goto _start;
}
}
}
else
{
uint8_t v___x_2887_; 
v___x_2887_ = 0;
return v___x_2887_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg___boxed(lean_object* v_k_2888_, lean_object* v_t_2889_){
_start:
{
uint8_t v_res_2890_; lean_object* v_r_2891_; 
v_res_2890_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(v_k_2888_, v_t_2889_);
lean_dec(v_t_2889_);
lean_dec(v_k_2888_);
v_r_2891_ = lean_box(v_res_2890_);
return v_r_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(lean_object* v_x_2892_, uint8_t v_bi_2893_, lean_object* v_t_2894_, lean_object* v_b_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v___y_2904_; lean_object* v___x_2907_; uint8_t v_debug_2908_; 
v___x_2907_ = lean_st_ref_get(v___y_2897_);
v_debug_2908_ = lean_ctor_get_uint8(v___x_2907_, sizeof(void*)*11);
lean_dec(v___x_2907_);
if (v_debug_2908_ == 0)
{
v___y_2904_ = v___y_2897_;
goto v___jp_2903_;
}
else
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2894_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v___x_2910_; 
lean_dec_ref_known(v___x_2909_, 1);
v___x_2910_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_dec_ref_known(v___x_2910_, 1);
v___y_2904_ = v___y_2897_;
goto v___jp_2903_;
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec_ref(v_b_2895_);
lean_dec_ref(v_t_2894_);
lean_dec(v_x_2892_);
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2910_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2910_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_dec_ref(v_b_2895_);
lean_dec_ref(v_t_2894_);
lean_dec(v_x_2892_);
v_a_2919_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2909_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2909_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
v___jp_2903_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2905_ = l_Lean_Expr_forallE___override(v_x_2892_, v_t_2894_, v_b_2895_, v_bi_2893_);
v___x_2906_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2905_, v___y_2904_);
return v___x_2906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg___boxed(lean_object* v_x_2927_, lean_object* v_bi_2928_, lean_object* v_t_2929_, lean_object* v_b_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
uint8_t v_bi_boxed_2938_; lean_object* v_res_2939_; 
v_bi_boxed_2938_ = lean_unbox(v_bi_2928_);
v_res_2939_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(v_x_2927_, v_bi_boxed_2938_, v_t_2929_, v_b_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(lean_object* v_d_2940_, lean_object* v_e_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
lean_object* v___y_2950_; lean_object* v___x_2953_; uint8_t v_debug_2954_; 
v___x_2953_ = lean_st_ref_get(v___y_2943_);
v_debug_2954_ = lean_ctor_get_uint8(v___x_2953_, sizeof(void*)*11);
lean_dec(v___x_2953_);
if (v_debug_2954_ == 0)
{
v___y_2950_ = v___y_2943_;
goto v___jp_2949_;
}
else
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_dec_ref_known(v___x_2955_, 1);
v___y_2950_ = v___y_2943_;
goto v___jp_2949_;
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
lean_dec_ref(v_e_2941_);
lean_dec(v_d_2940_);
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2955_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2955_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
v___jp_2949_:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2951_ = l_Lean_Expr_mdata___override(v_d_2940_, v_e_2941_);
v___x_2952_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2951_, v___y_2950_);
return v___x_2952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg___boxed(lean_object* v_d_2964_, lean_object* v_e_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(v_d_2964_, v_e_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(lean_object* v_structName_2974_, lean_object* v_idx_2975_, lean_object* v_struct_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
lean_object* v___y_2985_; lean_object* v___x_2988_; uint8_t v_debug_2989_; 
v___x_2988_ = lean_st_ref_get(v___y_2978_);
v_debug_2989_ = lean_ctor_get_uint8(v___x_2988_, sizeof(void*)*11);
lean_dec(v___x_2988_);
if (v_debug_2989_ == 0)
{
v___y_2985_ = v___y_2978_;
goto v___jp_2984_;
}
else
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_struct_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_dec_ref_known(v___x_2990_, 1);
v___y_2985_ = v___y_2978_;
goto v___jp_2984_;
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_dec_ref(v_struct_2976_);
lean_dec(v_idx_2975_);
lean_dec(v_structName_2974_);
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2990_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2990_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
v___jp_2984_:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = l_Lean_Expr_proj___override(v_structName_2974_, v_idx_2975_, v_struct_2976_);
v___x_2987_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2986_, v___y_2985_);
return v___x_2987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg___boxed(lean_object* v_structName_2999_, lean_object* v_idx_3000_, lean_object* v_struct_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(v_structName_2999_, v_idx_3000_, v_struct_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(lean_object* v_f_3010_, lean_object* v_a_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
lean_object* v___y_3020_; lean_object* v___x_3023_; uint8_t v_debug_3024_; 
v___x_3023_ = lean_st_ref_get(v___y_3013_);
v_debug_3024_ = lean_ctor_get_uint8(v___x_3023_, sizeof(void*)*11);
lean_dec(v___x_3023_);
if (v_debug_3024_ == 0)
{
v___y_3020_ = v___y_3013_;
goto v___jp_3019_;
}
else
{
lean_object* v___x_3025_; 
v___x_3025_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_3010_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v___x_3026_; 
lean_dec_ref_known(v___x_3025_, 1);
v___x_3026_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_dec_ref_known(v___x_3026_, 1);
v___y_3020_ = v___y_3013_;
goto v___jp_3019_;
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec_ref(v_a_3011_);
lean_dec_ref(v_f_3010_);
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3026_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3026_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
else
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_dec_ref(v_a_3011_);
lean_dec_ref(v_f_3010_);
v_a_3035_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_3025_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3025_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
v___jp_3019_:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3021_ = l_Lean_Expr_app___override(v_f_3010_, v_a_3011_);
v___x_3022_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_3021_, v___y_3020_);
return v___x_3022_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg___boxed(lean_object* v_f_3043_, lean_object* v_a_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(v_f_3043_, v_a_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(lean_object* v_a_3053_, lean_object* v_visited_3054_, lean_object* v_types_3055_, lean_object* v_subst_3056_, lean_object* v_a_x3f_3057_){
_start:
{
lean_object* v___x_3059_; lean_object* v_visitedClosed_3060_; lean_object* v_hasDepLetCache_3061_; lean_object* v_numConverted_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3072_; 
v___x_3059_ = lean_st_ref_take(v_a_3053_);
v_visitedClosed_3060_ = lean_ctor_get(v___x_3059_, 3);
v_hasDepLetCache_3061_ = lean_ctor_get(v___x_3059_, 4);
v_numConverted_3062_ = lean_ctor_get(v___x_3059_, 5);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3072_ == 0)
{
lean_object* v_unused_3073_; lean_object* v_unused_3074_; lean_object* v_unused_3075_; 
v_unused_3073_ = lean_ctor_get(v___x_3059_, 2);
lean_dec(v_unused_3073_);
v_unused_3074_ = lean_ctor_get(v___x_3059_, 1);
lean_dec(v_unused_3074_);
v_unused_3075_ = lean_ctor_get(v___x_3059_, 0);
lean_dec(v_unused_3075_);
v___x_3064_ = v___x_3059_;
v_isShared_3065_ = v_isSharedCheck_3072_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_numConverted_3062_);
lean_inc(v_hasDepLetCache_3061_);
lean_inc(v_visitedClosed_3060_);
lean_dec(v___x_3059_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3072_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3066_; lean_object* v___x_3068_; 
v___x_3066_ = lean_box(0);
if (v_isShared_3065_ == 0)
{
lean_ctor_set(v___x_3064_, 2, v_subst_3056_);
lean_ctor_set(v___x_3064_, 1, v_types_3055_);
lean_ctor_set(v___x_3064_, 0, v_visited_3054_);
v___x_3068_ = v___x_3064_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_visited_3054_);
lean_ctor_set(v_reuseFailAlloc_3071_, 1, v_types_3055_);
lean_ctor_set(v_reuseFailAlloc_3071_, 2, v_subst_3056_);
lean_ctor_set(v_reuseFailAlloc_3071_, 3, v_visitedClosed_3060_);
lean_ctor_set(v_reuseFailAlloc_3071_, 4, v_hasDepLetCache_3061_);
lean_ctor_set(v_reuseFailAlloc_3071_, 5, v_numConverted_3062_);
v___x_3068_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = lean_st_ref_put(v_a_3053_, v___x_3068_);
v___x_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3066_);
return v___x_3070_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0___boxed(lean_object* v_a_3076_, lean_object* v_visited_3077_, lean_object* v_types_3078_, lean_object* v_subst_3079_, lean_object* v_a_x3f_3080_, lean_object* v___y_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(v_a_3076_, v_visited_3077_, v_types_3078_, v_subst_3079_, v_a_x3f_3080_);
lean_dec(v_a_x3f_3080_);
lean_dec(v_a_3076_);
return v_res_3082_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3083_ = lean_unsigned_to_nat(32u);
v___x_3084_ = lean_mk_empty_array_with_capacity(v___x_3083_);
v___x_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
return v___x_3085_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1(void){
_start:
{
size_t v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3086_ = ((size_t)5ULL);
v___x_3087_ = lean_unsigned_to_nat(0u);
v___x_3088_ = lean_unsigned_to_nat(32u);
v___x_3089_ = lean_mk_empty_array_with_capacity(v___x_3088_);
v___x_3090_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0);
v___x_3091_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
lean_ctor_set(v___x_3091_, 1, v___x_3089_);
lean_ctor_set(v___x_3091_, 2, v___x_3087_);
lean_ctor_set(v___x_3091_, 3, v___x_3087_);
lean_ctor_set_usize(v___x_3091_, 4, v___x_3086_);
return v___x_3091_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2(void){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = lean_unsigned_to_nat(0u);
v___x_3093_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1);
v___x_3094_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
lean_ctor_set(v___x_3094_, 1, v___x_3092_);
lean_ctor_set(v___x_3094_, 2, v___x_3092_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0___boxed(lean_object* v_body_3095_, lean_object* v_binderType_3096_, lean_object* v_a_3097_, lean_object* v_binderName_3098_, lean_object* v_binderInfo_3099_, lean_object* v_e_3100_, lean_object* v_x_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
uint8_t v_binderInfo_76022__boxed_3111_; lean_object* v_res_3112_; 
v_binderInfo_76022__boxed_3111_ = lean_unbox(v_binderInfo_3099_);
v_res_3112_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0(v_body_3095_, v_binderType_3096_, v_a_3097_, v_binderName_3098_, v_binderInfo_76022__boxed_3111_, v_e_3100_, v_x_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec_ref(v_x_3101_);
lean_dec_ref(v_binderType_3096_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0(lean_object* v_body_3113_, lean_object* v_binderType_3114_, lean_object* v_a_3115_, lean_object* v_binderName_3116_, uint8_t v_binderInfo_3117_, lean_object* v_e_3118_, lean_object* v_x_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v___x_3129_; 
lean_inc_ref(v_body_3113_);
v___x_3129_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(v_body_3113_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3145_; 
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3132_ = v___x_3129_;
v_isShared_3133_ = v_isSharedCheck_3145_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3129_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3145_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
size_t v___x_3134_; size_t v___x_3135_; uint8_t v___x_3136_; 
v___x_3134_ = lean_ptr_addr(v_binderType_3114_);
v___x_3135_ = lean_ptr_addr(v_a_3115_);
v___x_3136_ = lean_usize_dec_eq(v___x_3134_, v___x_3135_);
if (v___x_3136_ == 0)
{
lean_object* v___x_3137_; 
lean_del_object(v___x_3132_);
lean_dec_ref(v_e_3118_);
lean_dec_ref(v_body_3113_);
v___x_3137_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(v_binderName_3116_, v_binderInfo_3117_, v_a_3115_, v_a_3130_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
return v___x_3137_;
}
else
{
size_t v___x_3138_; size_t v___x_3139_; uint8_t v___x_3140_; 
v___x_3138_ = lean_ptr_addr(v_body_3113_);
lean_dec_ref(v_body_3113_);
v___x_3139_ = lean_ptr_addr(v_a_3130_);
v___x_3140_ = lean_usize_dec_eq(v___x_3138_, v___x_3139_);
if (v___x_3140_ == 0)
{
lean_object* v___x_3141_; 
lean_del_object(v___x_3132_);
lean_dec_ref(v_e_3118_);
v___x_3141_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(v_binderName_3116_, v_binderInfo_3117_, v_a_3115_, v_a_3130_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
return v___x_3141_;
}
else
{
lean_object* v___x_3143_; 
lean_dec(v_a_3130_);
lean_dec(v_binderName_3116_);
lean_dec_ref(v_a_3115_);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 0, v_e_3118_);
v___x_3143_ = v___x_3132_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_e_3118_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3118_);
lean_dec(v_binderName_3116_);
lean_dec_ref(v_a_3115_);
lean_dec_ref(v_body_3113_);
return v___x_3129_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0___boxed(lean_object* v_body_3146_, lean_object* v_binderType_3147_, lean_object* v_a_3148_, lean_object* v_binderName_3149_, lean_object* v_binderInfo_3150_, lean_object* v_e_3151_, lean_object* v_x_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
uint8_t v_binderInfo_76049__boxed_3162_; lean_object* v_res_3163_; 
v_binderInfo_76049__boxed_3162_ = lean_unbox(v_binderInfo_3150_);
v_res_3163_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0(v_body_3146_, v_binderType_3147_, v_a_3148_, v_binderName_3149_, v_binderInfo_76049__boxed_3162_, v_e_3151_, v_x_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec_ref(v_x_3152_);
lean_dec_ref(v_binderType_3147_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(lean_object* v_e_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_){
_start:
{
if (lean_obj_tag(v_e_3164_) == 7)
{
lean_object* v_binderName_3174_; lean_object* v_binderType_3175_; lean_object* v_body_3176_; uint8_t v_binderInfo_3177_; lean_object* v___x_3178_; 
v_binderName_3174_ = lean_ctor_get(v_e_3164_, 0);
lean_inc(v_binderName_3174_);
v_binderType_3175_ = lean_ctor_get(v_e_3164_, 1);
lean_inc_ref_n(v_binderType_3175_, 2);
v_body_3176_ = lean_ctor_get(v_e_3164_, 2);
lean_inc_ref(v_body_3176_);
v_binderInfo_3177_ = lean_ctor_get_uint8(v_e_3164_, sizeof(void*)*3 + 8);
v___x_3178_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_binderType_3175_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v_a_3179_; lean_object* v___x_3180_; lean_object* v___f_3181_; lean_object* v___x_3182_; 
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
lean_inc_n(v_a_3179_, 2);
lean_dec_ref_known(v___x_3178_, 1);
v___x_3180_ = lean_box(v_binderInfo_3177_);
lean_inc(v_binderName_3174_);
lean_inc_ref(v_binderType_3175_);
v___f_3181_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0___boxed), 16, 6);
lean_closure_set(v___f_3181_, 0, v_body_3176_);
lean_closure_set(v___f_3181_, 1, v_binderType_3175_);
lean_closure_set(v___f_3181_, 2, v_a_3179_);
lean_closure_set(v___f_3181_, 3, v_binderName_3174_);
lean_closure_set(v___f_3181_, 4, v___x_3180_);
lean_closure_set(v___f_3181_, 5, v_e_3164_);
v___x_3182_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3179_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; lean_object* v___x_3184_; 
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
lean_inc_n(v_a_3183_, 2);
lean_dec_ref_known(v___x_3182_, 1);
v___x_3184_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_binderType_3175_, v_a_3183_, v_a_3165_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_cleanSuffix_3185_; lean_object* v___x_3186_; uint8_t v___y_3188_; lean_object* v___x_3191_; uint8_t v___x_3192_; 
lean_dec_ref_known(v___x_3184_, 1);
v_cleanSuffix_3185_ = lean_ctor_get(v_a_3165_, 2);
v___x_3186_ = lean_box(0);
v___x_3191_ = l_Lean_Expr_looseBVarRange(v_binderType_3175_);
lean_dec_ref(v_binderType_3175_);
v___x_3192_ = lean_nat_dec_le(v___x_3191_, v_cleanSuffix_3185_);
lean_dec(v___x_3191_);
if (v___x_3192_ == 0)
{
uint8_t v___x_3193_; 
v___x_3193_ = 1;
v___y_3188_ = v___x_3193_;
goto v___jp_3187_;
}
else
{
uint8_t v___x_3194_; 
v___x_3194_ = 0;
v___y_3188_ = v___x_3194_;
goto v___jp_3187_;
}
v___jp_3187_:
{
uint8_t v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = 0;
v___x_3190_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_binderName_3174_, v_a_3183_, v___x_3186_, v___y_3188_, v___x_3189_, v___f_3181_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_);
return v___x_3190_;
}
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_dec(v_a_3183_);
lean_dec_ref(v___f_3181_);
lean_dec_ref(v_binderType_3175_);
lean_dec(v_binderName_3174_);
v_a_3195_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3184_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3184_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
else
{
lean_dec_ref(v___f_3181_);
lean_dec_ref(v_binderType_3175_);
lean_dec(v_binderName_3174_);
return v___x_3182_;
}
}
else
{
lean_dec_ref(v_body_3176_);
lean_dec_ref(v_binderType_3175_);
lean_dec(v_binderName_3174_);
lean_dec_ref_known(v_e_3164_, 3);
return v___x_3178_;
}
}
else
{
lean_object* v___x_3203_; 
lean_inc_ref(v_e_3164_);
v___x_3203_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_e_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v_numCandidates_3205_; lean_object* v_cleanSuffix_3206_; lean_object* v___x_3207_; uint8_t v___x_3208_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_a_3204_);
v_numCandidates_3205_ = lean_ctor_get(v_a_3165_, 1);
v_cleanSuffix_3206_ = lean_ctor_get(v_a_3165_, 2);
v___x_3207_ = lean_unsigned_to_nat(0u);
v___x_3208_ = lean_nat_dec_lt(v___x_3207_, v_numCandidates_3205_);
if (v___x_3208_ == 0)
{
lean_dec(v_a_3204_);
lean_dec_ref(v_e_3164_);
return v___x_3203_;
}
else
{
lean_object* v___x_3209_; uint8_t v___x_3210_; 
v___x_3209_ = l_Lean_Expr_looseBVarRange(v_e_3164_);
lean_dec_ref(v_e_3164_);
v___x_3210_ = lean_nat_dec_le(v___x_3209_, v_cleanSuffix_3206_);
lean_dec(v___x_3209_);
if (v___x_3210_ == 0)
{
lean_object* v___x_3211_; 
lean_dec_ref_known(v___x_3203_, 1);
lean_inc(v_a_3204_);
v___x_3211_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3204_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3213_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_a_3212_);
lean_dec_ref_known(v___x_3211_, 1);
v___x_3213_ = l_Lean_Meta_getLevel(v_a_3212_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3220_ == 0)
{
lean_object* v_unused_3221_; 
v_unused_3221_ = lean_ctor_get(v___x_3213_, 0);
lean_dec(v_unused_3221_);
v___x_3215_ = v___x_3213_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_dec(v___x_3213_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 0, v_a_3204_);
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3204_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
else
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
lean_dec(v_a_3204_);
v_a_3222_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3224_ = v___x_3213_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3213_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3227_; 
if (v_isShared_3225_ == 0)
{
v___x_3227_ = v___x_3224_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3222_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
else
{
lean_dec(v_a_3204_);
return v___x_3211_;
}
}
else
{
lean_dec(v_a_3204_);
return v___x_3203_;
}
}
}
else
{
lean_dec_ref(v_e_3164_);
return v___x_3203_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1(lean_object* v_body_3230_, lean_object* v_type_3231_, lean_object* v_a_3232_, lean_object* v_declName_3233_, lean_object* v_a_3234_, uint8_t v_nondep_3235_, lean_object* v_value_3236_, lean_object* v_e_3237_, uint8_t v___y_3238_, lean_object* v_x_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v___x_3249_; 
lean_inc_ref(v_body_3230_);
v___x_3249_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_body_3230_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3316_; 
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3252_ = v___x_3249_;
v_isShared_3253_ = v_isSharedCheck_3316_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3249_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3316_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; uint8_t v_nondep_x27_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___x_3286_; 
v___x_3286_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v___y_3245_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; uint8_t v___x_3288_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3287_);
lean_dec_ref_known(v___x_3286_, 1);
v___x_3288_ = 1;
if (v_nondep_3235_ == 0)
{
if (v___y_3238_ == 0)
{
lean_dec(v_a_3287_);
v_nondep_x27_3277_ = v_nondep_3235_;
v___y_3278_ = v___y_3242_;
v___y_3279_ = v___y_3243_;
v___y_3280_ = v___y_3244_;
v___y_3281_ = v___y_3245_;
v___y_3282_ = v___y_3246_;
v___y_3283_ = v___y_3247_;
goto v___jp_3276_;
}
else
{
lean_object* v___x_3289_; uint8_t v___x_3290_; 
v___x_3289_ = l_Lean_Expr_fvarId_x21(v_x_3239_);
v___x_3290_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(v___x_3289_, v_a_3287_);
lean_dec(v_a_3287_);
lean_dec(v___x_3289_);
if (v___x_3290_ == 0)
{
lean_object* v___x_3291_; lean_object* v_visited_3292_; lean_object* v_types_3293_; lean_object* v_subst_3294_; lean_object* v_visitedClosed_3295_; lean_object* v_hasDepLetCache_3296_; lean_object* v_numConverted_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3307_; 
v___x_3291_ = lean_st_ref_take(v___y_3241_);
v_visited_3292_ = lean_ctor_get(v___x_3291_, 0);
v_types_3293_ = lean_ctor_get(v___x_3291_, 1);
v_subst_3294_ = lean_ctor_get(v___x_3291_, 2);
v_visitedClosed_3295_ = lean_ctor_get(v___x_3291_, 3);
v_hasDepLetCache_3296_ = lean_ctor_get(v___x_3291_, 4);
v_numConverted_3297_ = lean_ctor_get(v___x_3291_, 5);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3299_ = v___x_3291_;
v_isShared_3300_ = v_isSharedCheck_3307_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_numConverted_3297_);
lean_inc(v_hasDepLetCache_3296_);
lean_inc(v_visitedClosed_3295_);
lean_inc(v_subst_3294_);
lean_inc(v_types_3293_);
lean_inc(v_visited_3292_);
lean_dec(v___x_3291_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3307_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3304_; 
v___x_3301_ = lean_unsigned_to_nat(1u);
v___x_3302_ = lean_nat_add(v_numConverted_3297_, v___x_3301_);
lean_dec(v_numConverted_3297_);
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 5, v___x_3302_);
v___x_3304_ = v___x_3299_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_visited_3292_);
lean_ctor_set(v_reuseFailAlloc_3306_, 1, v_types_3293_);
lean_ctor_set(v_reuseFailAlloc_3306_, 2, v_subst_3294_);
lean_ctor_set(v_reuseFailAlloc_3306_, 3, v_visitedClosed_3295_);
lean_ctor_set(v_reuseFailAlloc_3306_, 4, v_hasDepLetCache_3296_);
lean_ctor_set(v_reuseFailAlloc_3306_, 5, v___x_3302_);
v___x_3304_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
lean_object* v___x_3305_; 
v___x_3305_ = lean_st_ref_put(v___y_3241_, v___x_3304_);
v_nondep_x27_3277_ = v___x_3288_;
v___y_3278_ = v___y_3242_;
v___y_3279_ = v___y_3243_;
v___y_3280_ = v___y_3244_;
v___y_3281_ = v___y_3245_;
v___y_3282_ = v___y_3246_;
v___y_3283_ = v___y_3247_;
goto v___jp_3276_;
}
}
}
else
{
v_nondep_x27_3277_ = v_nondep_3235_;
v___y_3278_ = v___y_3242_;
v___y_3279_ = v___y_3243_;
v___y_3280_ = v___y_3244_;
v___y_3281_ = v___y_3245_;
v___y_3282_ = v___y_3246_;
v___y_3283_ = v___y_3247_;
goto v___jp_3276_;
}
}
}
else
{
lean_dec(v_a_3287_);
v_nondep_x27_3277_ = v___x_3288_;
v___y_3278_ = v___y_3242_;
v___y_3279_ = v___y_3243_;
v___y_3280_ = v___y_3244_;
v___y_3281_ = v___y_3245_;
v___y_3282_ = v___y_3246_;
v___y_3283_ = v___y_3247_;
goto v___jp_3276_;
}
}
else
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
lean_del_object(v___x_3252_);
lean_dec(v_a_3250_);
lean_dec_ref(v_e_3237_);
lean_dec_ref(v_a_3234_);
lean_dec(v_declName_3233_);
lean_dec_ref(v_a_3232_);
lean_dec_ref(v_body_3230_);
v_a_3308_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3310_ = v___x_3286_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3286_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3308_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
v___jp_3254_:
{
size_t v___x_3261_; size_t v___x_3262_; uint8_t v___x_3263_; 
v___x_3261_ = lean_ptr_addr(v_type_3231_);
v___x_3262_ = lean_ptr_addr(v_a_3232_);
v___x_3263_ = lean_usize_dec_eq(v___x_3261_, v___x_3262_);
if (v___x_3263_ == 0)
{
lean_object* v___x_3264_; 
lean_del_object(v___x_3252_);
lean_dec_ref(v_e_3237_);
lean_dec_ref(v_body_3230_);
v___x_3264_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3233_, v_a_3232_, v_a_3234_, v_a_3250_, v_nondep_3235_, v___y_3258_, v___y_3255_, v___y_3259_, v___y_3257_, v___y_3260_, v___y_3256_);
return v___x_3264_;
}
else
{
size_t v___x_3265_; size_t v___x_3266_; uint8_t v___x_3267_; 
v___x_3265_ = lean_ptr_addr(v_value_3236_);
v___x_3266_ = lean_ptr_addr(v_a_3234_);
v___x_3267_ = lean_usize_dec_eq(v___x_3265_, v___x_3266_);
if (v___x_3267_ == 0)
{
lean_object* v___x_3268_; 
lean_del_object(v___x_3252_);
lean_dec_ref(v_e_3237_);
lean_dec_ref(v_body_3230_);
v___x_3268_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3233_, v_a_3232_, v_a_3234_, v_a_3250_, v_nondep_3235_, v___y_3258_, v___y_3255_, v___y_3259_, v___y_3257_, v___y_3260_, v___y_3256_);
return v___x_3268_;
}
else
{
size_t v___x_3269_; size_t v___x_3270_; uint8_t v___x_3271_; 
v___x_3269_ = lean_ptr_addr(v_body_3230_);
lean_dec_ref(v_body_3230_);
v___x_3270_ = lean_ptr_addr(v_a_3250_);
v___x_3271_ = lean_usize_dec_eq(v___x_3269_, v___x_3270_);
if (v___x_3271_ == 0)
{
lean_object* v___x_3272_; 
lean_del_object(v___x_3252_);
lean_dec_ref(v_e_3237_);
v___x_3272_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3233_, v_a_3232_, v_a_3234_, v_a_3250_, v_nondep_3235_, v___y_3258_, v___y_3255_, v___y_3259_, v___y_3257_, v___y_3260_, v___y_3256_);
return v___x_3272_;
}
else
{
lean_object* v___x_3274_; 
lean_dec(v_a_3250_);
lean_dec_ref(v_a_3234_);
lean_dec(v_declName_3233_);
lean_dec_ref(v_a_3232_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v_e_3237_);
v___x_3274_ = v___x_3252_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_e_3237_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
}
v___jp_3276_:
{
if (v_nondep_3235_ == 0)
{
if (v_nondep_x27_3277_ == 0)
{
v___y_3255_ = v___y_3279_;
v___y_3256_ = v___y_3283_;
v___y_3257_ = v___y_3281_;
v___y_3258_ = v___y_3278_;
v___y_3259_ = v___y_3280_;
v___y_3260_ = v___y_3282_;
goto v___jp_3254_;
}
else
{
lean_object* v___x_3284_; 
lean_del_object(v___x_3252_);
lean_dec_ref(v_e_3237_);
lean_dec_ref(v_body_3230_);
v___x_3284_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3233_, v_a_3232_, v_a_3234_, v_a_3250_, v_nondep_x27_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
return v___x_3284_;
}
}
else
{
if (v_nondep_x27_3277_ == 0)
{
lean_object* v___x_3285_; 
lean_del_object(v___x_3252_);
lean_dec_ref(v_e_3237_);
lean_dec_ref(v_body_3230_);
v___x_3285_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3233_, v_a_3232_, v_a_3234_, v_a_3250_, v_nondep_x27_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
return v___x_3285_;
}
else
{
v___y_3255_ = v___y_3279_;
v___y_3256_ = v___y_3283_;
v___y_3257_ = v___y_3281_;
v___y_3258_ = v___y_3278_;
v___y_3259_ = v___y_3280_;
v___y_3260_ = v___y_3282_;
goto v___jp_3254_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3237_);
lean_dec_ref(v_a_3234_);
lean_dec(v_declName_3233_);
lean_dec_ref(v_a_3232_);
lean_dec_ref(v_body_3230_);
return v___x_3249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1___boxed(lean_object** _args){
lean_object* v_body_3317_ = _args[0];
lean_object* v_type_3318_ = _args[1];
lean_object* v_a_3319_ = _args[2];
lean_object* v_declName_3320_ = _args[3];
lean_object* v_a_3321_ = _args[4];
lean_object* v_nondep_3322_ = _args[5];
lean_object* v_value_3323_ = _args[6];
lean_object* v_e_3324_ = _args[7];
lean_object* v___y_3325_ = _args[8];
lean_object* v_x_3326_ = _args[9];
lean_object* v___y_3327_ = _args[10];
lean_object* v___y_3328_ = _args[11];
lean_object* v___y_3329_ = _args[12];
lean_object* v___y_3330_ = _args[13];
lean_object* v___y_3331_ = _args[14];
lean_object* v___y_3332_ = _args[15];
lean_object* v___y_3333_ = _args[16];
lean_object* v___y_3334_ = _args[17];
lean_object* v___y_3335_ = _args[18];
_start:
{
uint8_t v_nondep_76205__boxed_3336_; uint8_t v___y_76207__boxed_3337_; lean_object* v_res_3338_; 
v_nondep_76205__boxed_3336_ = lean_unbox(v_nondep_3322_);
v___y_76207__boxed_3337_ = lean_unbox(v___y_3325_);
v_res_3338_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1(v_body_3317_, v_type_3318_, v_a_3319_, v_declName_3320_, v_a_3321_, v_nondep_76205__boxed_3336_, v_value_3323_, v_e_3324_, v___y_76207__boxed_3337_, v_x_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec_ref(v_x_3326_);
lean_dec_ref(v_value_3323_);
lean_dec_ref(v_type_3318_);
return v_res_3338_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1(void){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3340_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_3341_ = lean_unsigned_to_nat(9u);
v___x_3342_ = lean_unsigned_to_nat(263u);
v___x_3343_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__0));
v___x_3344_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0));
v___x_3345_ = l_mkPanicMessageWithDecl(v___x_3344_, v___x_3343_, v___x_3342_, v___x_3341_, v___x_3340_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(lean_object* v_e_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_){
_start:
{
switch(lean_obj_tag(v_e_3346_))
{
case 5:
{
lean_object* v_fn_3356_; lean_object* v_arg_3357_; lean_object* v___y_3359_; lean_object* v_a_3360_; lean_object* v___y_3382_; lean_object* v___x_3384_; 
v_fn_3356_ = lean_ctor_get(v_e_3346_, 0);
lean_inc_ref_n(v_fn_3356_, 2);
v_arg_3357_ = lean_ctor_get(v_e_3346_, 1);
lean_inc_ref(v_arg_3357_);
v___x_3384_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_fn_3356_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3386_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3384_, 1);
lean_inc_ref(v_arg_3357_);
v___x_3386_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_arg_3357_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3402_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3389_ = v___x_3386_;
v_isShared_3390_ = v_isSharedCheck_3402_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3386_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3402_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
size_t v___x_3391_; size_t v___x_3392_; uint8_t v___x_3393_; 
v___x_3391_ = lean_ptr_addr(v_fn_3356_);
v___x_3392_ = lean_ptr_addr(v_a_3385_);
v___x_3393_ = lean_usize_dec_eq(v___x_3391_, v___x_3392_);
if (v___x_3393_ == 0)
{
lean_object* v___x_3394_; 
lean_del_object(v___x_3389_);
lean_dec_ref_known(v_e_3346_, 2);
v___x_3394_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(v_a_3385_, v_a_3387_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
v___y_3382_ = v___x_3394_;
goto v___jp_3381_;
}
else
{
size_t v___x_3395_; size_t v___x_3396_; uint8_t v___x_3397_; 
v___x_3395_ = lean_ptr_addr(v_arg_3357_);
v___x_3396_ = lean_ptr_addr(v_a_3387_);
v___x_3397_ = lean_usize_dec_eq(v___x_3395_, v___x_3396_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3398_; 
lean_del_object(v___x_3389_);
lean_dec_ref_known(v_e_3346_, 2);
v___x_3398_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(v_a_3385_, v_a_3387_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
v___y_3382_ = v___x_3398_;
goto v___jp_3381_;
}
else
{
lean_object* v___x_3400_; 
lean_dec(v_a_3387_);
lean_dec(v_a_3385_);
lean_inc_ref(v_e_3346_);
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 0, v_e_3346_);
v___x_3400_ = v___x_3389_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_e_3346_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
v___y_3359_ = v___x_3400_;
v_a_3360_ = v_e_3346_;
goto v___jp_3358_;
}
}
}
}
}
else
{
lean_dec(v_a_3385_);
lean_dec_ref(v_arg_3357_);
lean_dec_ref_known(v_e_3346_, 2);
lean_dec_ref(v_fn_3356_);
return v___x_3386_;
}
}
else
{
lean_dec_ref(v_arg_3357_);
lean_dec_ref_known(v_e_3346_, 2);
lean_dec_ref(v_fn_3356_);
return v___x_3384_;
}
v___jp_3358_:
{
lean_object* v_numCandidates_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v_numCandidates_3361_ = lean_ctor_get(v_a_3347_, 1);
v___x_3362_ = lean_unsigned_to_nat(0u);
v___x_3363_ = lean_nat_dec_lt(v___x_3362_, v_numCandidates_3361_);
if (v___x_3363_ == 0)
{
lean_dec_ref(v_a_3360_);
lean_dec_ref(v_arg_3357_);
lean_dec_ref(v_fn_3356_);
return v___y_3359_;
}
else
{
lean_object* v___x_3364_; 
lean_dec_ref(v___y_3359_);
v___x_3364_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp(v_fn_3356_, v_arg_3357_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3371_; 
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3371_ == 0)
{
lean_object* v_unused_3372_; 
v_unused_3372_ = lean_ctor_get(v___x_3364_, 0);
lean_dec(v_unused_3372_);
v___x_3366_ = v___x_3364_;
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
else
{
lean_dec(v___x_3364_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v_a_3360_);
v___x_3369_ = v___x_3366_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3360_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
lean_dec_ref(v_a_3360_);
v_a_3373_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3364_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3364_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
}
v___jp_3381_:
{
if (lean_obj_tag(v___y_3382_) == 0)
{
lean_object* v_a_3383_; 
v_a_3383_ = lean_ctor_get(v___y_3382_, 0);
lean_inc(v_a_3383_);
v___y_3359_ = v___y_3382_;
v_a_3360_ = v_a_3383_;
goto v___jp_3358_;
}
else
{
lean_dec_ref(v_arg_3357_);
lean_dec_ref(v_fn_3356_);
return v___y_3382_;
}
}
}
case 10:
{
lean_object* v_data_3403_; lean_object* v_expr_3404_; lean_object* v___x_3405_; 
v_data_3403_ = lean_ctor_get(v_e_3346_, 0);
v_expr_3404_ = lean_ctor_get(v_e_3346_, 1);
lean_inc_ref(v_expr_3404_);
v___x_3405_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_expr_3404_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3417_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3408_ = v___x_3405_;
v_isShared_3409_ = v_isSharedCheck_3417_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3405_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3417_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
size_t v___x_3410_; size_t v___x_3411_; uint8_t v___x_3412_; 
v___x_3410_ = lean_ptr_addr(v_expr_3404_);
v___x_3411_ = lean_ptr_addr(v_a_3406_);
v___x_3412_ = lean_usize_dec_eq(v___x_3410_, v___x_3411_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; 
lean_inc(v_data_3403_);
lean_del_object(v___x_3408_);
lean_dec_ref_known(v_e_3346_, 2);
v___x_3413_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(v_data_3403_, v_a_3406_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
return v___x_3413_;
}
else
{
lean_object* v___x_3415_; 
lean_dec(v_a_3406_);
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v_e_3346_);
v___x_3415_ = v___x_3408_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_e_3346_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3346_, 2);
return v___x_3405_;
}
}
case 11:
{
lean_object* v_typeName_3418_; lean_object* v_idx_3419_; lean_object* v_struct_3420_; lean_object* v___y_3422_; lean_object* v_a_3423_; lean_object* v___x_3439_; 
v_typeName_3418_ = lean_ctor_get(v_e_3346_, 0);
v_idx_3419_ = lean_ctor_get(v_e_3346_, 1);
v_struct_3420_ = lean_ctor_get(v_e_3346_, 2);
lean_inc_ref(v_struct_3420_);
v___x_3439_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_struct_3420_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3452_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3442_ = v___x_3439_;
v_isShared_3443_ = v_isSharedCheck_3452_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3439_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3452_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
size_t v___x_3444_; size_t v___x_3445_; uint8_t v___x_3446_; 
v___x_3444_ = lean_ptr_addr(v_struct_3420_);
v___x_3445_ = lean_ptr_addr(v_a_3440_);
v___x_3446_ = lean_usize_dec_eq(v___x_3444_, v___x_3445_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; 
lean_del_object(v___x_3442_);
lean_inc(v_idx_3419_);
lean_inc(v_typeName_3418_);
v___x_3447_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(v_typeName_3418_, v_idx_3419_, v_a_3440_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_a_3448_);
v___y_3422_ = v___x_3447_;
v_a_3423_ = v_a_3448_;
goto v___jp_3421_;
}
else
{
lean_dec_ref_known(v_e_3346_, 3);
return v___x_3447_;
}
}
else
{
lean_object* v___x_3450_; 
lean_dec(v_a_3440_);
lean_inc_ref(v_e_3346_);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 0, v_e_3346_);
v___x_3450_ = v___x_3442_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_e_3346_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_inc_ref(v_e_3346_);
v___y_3422_ = v___x_3450_;
v_a_3423_ = v_e_3346_;
goto v___jp_3421_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3346_, 3);
return v___x_3439_;
}
v___jp_3421_:
{
lean_object* v_numCandidates_3424_; lean_object* v_cleanSuffix_3425_; lean_object* v___x_3426_; uint8_t v___x_3427_; 
v_numCandidates_3424_ = lean_ctor_get(v_a_3347_, 1);
v_cleanSuffix_3425_ = lean_ctor_get(v_a_3347_, 2);
v___x_3426_ = lean_unsigned_to_nat(0u);
v___x_3427_ = lean_nat_dec_lt(v___x_3426_, v_numCandidates_3424_);
if (v___x_3427_ == 0)
{
lean_dec_ref(v_a_3423_);
lean_dec_ref_known(v_e_3346_, 3);
return v___y_3422_;
}
else
{
lean_object* v___x_3428_; uint8_t v___x_3429_; 
v___x_3428_ = l_Lean_Expr_looseBVarRange(v_struct_3420_);
v___x_3429_ = lean_nat_dec_le(v___x_3428_, v_cleanSuffix_3425_);
lean_dec(v___x_3428_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; 
lean_dec_ref(v___y_3422_);
v___x_3430_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(v_e_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3437_ == 0)
{
lean_object* v_unused_3438_; 
v_unused_3438_ = lean_ctor_get(v___x_3430_, 0);
lean_dec(v_unused_3438_);
v___x_3432_ = v___x_3430_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_dec(v___x_3430_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 0, v_a_3423_);
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3423_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
else
{
lean_dec_ref(v_a_3423_);
return v___x_3430_;
}
}
else
{
lean_dec_ref(v_a_3423_);
lean_dec_ref_known(v_e_3346_, 3);
return v___y_3422_;
}
}
}
}
case 6:
{
lean_object* v_binderName_3453_; lean_object* v_binderType_3454_; lean_object* v_body_3455_; uint8_t v_binderInfo_3456_; lean_object* v___x_3457_; 
v_binderName_3453_ = lean_ctor_get(v_e_3346_, 0);
lean_inc(v_binderName_3453_);
v_binderType_3454_ = lean_ctor_get(v_e_3346_, 1);
lean_inc_ref_n(v_binderType_3454_, 2);
v_body_3455_ = lean_ctor_get(v_e_3346_, 2);
lean_inc_ref(v_body_3455_);
v_binderInfo_3456_ = lean_ctor_get_uint8(v_e_3346_, sizeof(void*)*3 + 8);
v___x_3457_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_binderType_3454_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3459_; lean_object* v___f_3460_; lean_object* v___x_3461_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc_n(v_a_3458_, 2);
lean_dec_ref_known(v___x_3457_, 1);
v___x_3459_ = lean_box(v_binderInfo_3456_);
lean_inc(v_binderName_3453_);
lean_inc_ref(v_binderType_3454_);
v___f_3460_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0___boxed), 16, 6);
lean_closure_set(v___f_3460_, 0, v_body_3455_);
lean_closure_set(v___f_3460_, 1, v_binderType_3454_);
lean_closure_set(v___f_3460_, 2, v_a_3458_);
lean_closure_set(v___f_3460_, 3, v_binderName_3453_);
lean_closure_set(v___f_3460_, 4, v___x_3459_);
lean_closure_set(v___f_3460_, 5, v_e_3346_);
v___x_3461_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3458_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; lean_object* v___x_3463_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc_n(v_a_3462_, 2);
lean_dec_ref_known(v___x_3461_, 1);
v___x_3463_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_binderType_3454_, v_a_3462_, v_a_3347_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_cleanSuffix_3464_; lean_object* v___x_3465_; uint8_t v___y_3467_; lean_object* v___x_3470_; uint8_t v___x_3471_; 
lean_dec_ref_known(v___x_3463_, 1);
v_cleanSuffix_3464_ = lean_ctor_get(v_a_3347_, 2);
v___x_3465_ = lean_box(0);
v___x_3470_ = l_Lean_Expr_looseBVarRange(v_binderType_3454_);
lean_dec_ref(v_binderType_3454_);
v___x_3471_ = lean_nat_dec_le(v___x_3470_, v_cleanSuffix_3464_);
lean_dec(v___x_3470_);
if (v___x_3471_ == 0)
{
uint8_t v___x_3472_; 
v___x_3472_ = 1;
v___y_3467_ = v___x_3472_;
goto v___jp_3466_;
}
else
{
uint8_t v___x_3473_; 
v___x_3473_ = 0;
v___y_3467_ = v___x_3473_;
goto v___jp_3466_;
}
v___jp_3466_:
{
uint8_t v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = 0;
v___x_3469_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_binderName_3453_, v_a_3462_, v___x_3465_, v___y_3467_, v___x_3468_, v___f_3460_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
return v___x_3469_;
}
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
lean_dec(v_a_3462_);
lean_dec_ref(v___f_3460_);
lean_dec_ref(v_binderType_3454_);
lean_dec(v_binderName_3453_);
v_a_3474_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3463_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3463_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
else
{
lean_dec_ref(v___f_3460_);
lean_dec_ref(v_binderType_3454_);
lean_dec(v_binderName_3453_);
return v___x_3461_;
}
}
else
{
lean_dec_ref(v_body_3455_);
lean_dec_ref(v_binderType_3454_);
lean_dec(v_binderName_3453_);
lean_dec_ref_known(v_e_3346_, 3);
return v___x_3457_;
}
}
case 7:
{
lean_object* v___x_3482_; 
v___x_3482_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(v_e_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
return v___x_3482_;
}
case 8:
{
lean_object* v_declName_3483_; lean_object* v_type_3484_; lean_object* v_value_3485_; lean_object* v_body_3486_; uint8_t v_nondep_3487_; lean_object* v___x_3488_; 
v_declName_3483_ = lean_ctor_get(v_e_3346_, 0);
lean_inc(v_declName_3483_);
v_type_3484_ = lean_ctor_get(v_e_3346_, 1);
lean_inc_ref_n(v_type_3484_, 2);
v_value_3485_ = lean_ctor_get(v_e_3346_, 2);
lean_inc_ref(v_value_3485_);
v_body_3486_ = lean_ctor_get(v_e_3346_, 3);
lean_inc_ref(v_body_3486_);
v_nondep_3487_ = lean_ctor_get_uint8(v_e_3346_, sizeof(void*)*4 + 8);
v___x_3488_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_type_3484_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v___x_3490_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v___x_3488_, 1);
lean_inc_ref(v_value_3485_);
v___x_3490_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_value_3485_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; lean_object* v___x_3492_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_a_3491_);
lean_dec_ref_known(v___x_3490_, 1);
lean_inc(v_a_3489_);
v___x_3492_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3489_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3577_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3495_ = v___x_3492_;
v_isShared_3496_ = v_isSharedCheck_3577_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3492_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3577_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v_numCandidates_3497_; lean_object* v_cleanSuffix_3498_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; uint8_t v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; uint8_t v___y_3510_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___x_3540_; uint8_t v___x_3541_; 
v_numCandidates_3497_ = lean_ctor_get(v_a_3347_, 1);
v_cleanSuffix_3498_ = lean_ctor_get(v_a_3347_, 2);
v___x_3540_ = lean_unsigned_to_nat(0u);
v___x_3541_ = lean_nat_dec_lt(v___x_3540_, v_numCandidates_3497_);
if (v___x_3541_ == 0)
{
v___y_3526_ = v_a_3347_;
v___y_3527_ = v_a_3348_;
v___y_3528_ = v_a_3349_;
v___y_3529_ = v_a_3350_;
v___y_3530_ = v_a_3351_;
v___y_3531_ = v_a_3352_;
v___y_3532_ = v_a_3353_;
v___y_3533_ = v_a_3354_;
goto v___jp_3525_;
}
else
{
lean_object* v___x_3542_; 
lean_inc(v_a_3493_);
v___x_3542_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_type_3484_, v_a_3493_, v_a_3347_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v___x_3565_; uint8_t v___x_3566_; 
lean_dec_ref_known(v___x_3542_, 1);
v___x_3565_ = l_Lean_Expr_looseBVarRange(v_type_3484_);
v___x_3566_ = lean_nat_dec_le(v___x_3565_, v_cleanSuffix_3498_);
lean_dec(v___x_3565_);
if (v___x_3566_ == 0)
{
goto v___jp_3543_;
}
else
{
lean_object* v___x_3567_; uint8_t v___x_3568_; 
v___x_3567_ = l_Lean_Expr_looseBVarRange(v_value_3485_);
v___x_3568_ = lean_nat_dec_le(v___x_3567_, v_cleanSuffix_3498_);
lean_dec(v___x_3567_);
if (v___x_3568_ == 0)
{
goto v___jp_3543_;
}
else
{
v___y_3526_ = v_a_3347_;
v___y_3527_ = v_a_3348_;
v___y_3528_ = v_a_3349_;
v___y_3529_ = v_a_3350_;
v___y_3530_ = v_a_3351_;
v___y_3531_ = v_a_3352_;
v___y_3532_ = v_a_3353_;
v___y_3533_ = v_a_3354_;
goto v___jp_3525_;
}
}
v___jp_3543_:
{
uint8_t v___x_3544_; 
v___x_3544_ = l_Lean_Expr_isLambda(v_value_3485_);
if (v___x_3544_ == 0)
{
lean_object* v___x_3545_; 
lean_inc_ref(v_value_3485_);
v___x_3545_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_value_3485_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v_a_3546_; lean_object* v___x_3547_; 
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3546_);
lean_dec_ref_known(v___x_3545_, 1);
lean_inc(v_a_3493_);
v___x_3547_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_a_3546_, v_a_3493_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_dec_ref_known(v___x_3547_, 1);
v___y_3526_ = v_a_3347_;
v___y_3527_ = v_a_3348_;
v___y_3528_ = v_a_3349_;
v___y_3529_ = v_a_3350_;
v___y_3530_ = v_a_3351_;
v___y_3531_ = v_a_3352_;
v___y_3532_ = v_a_3353_;
v___y_3533_ = v_a_3354_;
goto v___jp_3525_;
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
lean_del_object(v___x_3495_);
lean_dec(v_a_3493_);
lean_dec(v_a_3491_);
lean_dec(v_a_3489_);
lean_dec_ref(v_body_3486_);
lean_dec_ref(v_value_3485_);
lean_dec_ref(v_type_3484_);
lean_dec(v_declName_3483_);
lean_dec_ref_known(v_e_3346_, 4);
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3547_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3547_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
else
{
lean_del_object(v___x_3495_);
lean_dec(v_a_3493_);
lean_dec(v_a_3491_);
lean_dec(v_a_3489_);
lean_dec_ref(v_body_3486_);
lean_dec_ref(v_value_3485_);
lean_dec_ref(v_type_3484_);
lean_dec(v_declName_3483_);
lean_dec_ref_known(v_e_3346_, 4);
return v___x_3545_;
}
}
else
{
lean_object* v___x_3556_; 
lean_inc(v_a_3493_);
lean_inc_ref(v_value_3485_);
v___x_3556_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_value_3485_, v_a_3493_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_dec_ref_known(v___x_3556_, 1);
v___y_3526_ = v_a_3347_;
v___y_3527_ = v_a_3348_;
v___y_3528_ = v_a_3349_;
v___y_3529_ = v_a_3350_;
v___y_3530_ = v_a_3351_;
v___y_3531_ = v_a_3352_;
v___y_3532_ = v_a_3353_;
v___y_3533_ = v_a_3354_;
goto v___jp_3525_;
}
else
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3564_; 
lean_del_object(v___x_3495_);
lean_dec(v_a_3493_);
lean_dec(v_a_3491_);
lean_dec(v_a_3489_);
lean_dec_ref(v_body_3486_);
lean_dec_ref(v_value_3485_);
lean_dec_ref(v_type_3484_);
lean_dec(v_declName_3483_);
lean_dec_ref_known(v_e_3346_, 4);
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3559_ = v___x_3556_;
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3556_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3557_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
}
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_del_object(v___x_3495_);
lean_dec(v_a_3493_);
lean_dec(v_a_3491_);
lean_dec(v_a_3489_);
lean_dec_ref(v_body_3486_);
lean_dec_ref(v_value_3485_);
lean_dec_ref(v_type_3484_);
lean_dec(v_declName_3483_);
lean_dec_ref_known(v_e_3346_, 4);
v_a_3569_ = lean_ctor_get(v___x_3542_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3542_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3542_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
v___jp_3499_:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___f_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3517_; 
v___x_3511_ = lean_box(v_nondep_3487_);
v___x_3512_ = lean_box(v___y_3510_);
lean_inc(v_declName_3483_);
lean_inc_ref(v_type_3484_);
v___f_3513_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1___boxed), 19, 9);
lean_closure_set(v___f_3513_, 0, v_body_3486_);
lean_closure_set(v___f_3513_, 1, v_type_3484_);
lean_closure_set(v___f_3513_, 2, v_a_3489_);
lean_closure_set(v___f_3513_, 3, v_declName_3483_);
lean_closure_set(v___f_3513_, 4, v_a_3491_);
lean_closure_set(v___f_3513_, 5, v___x_3511_);
lean_closure_set(v___f_3513_, 6, v_value_3485_);
lean_closure_set(v___f_3513_, 7, v_e_3346_);
lean_closure_set(v___f_3513_, 8, v___x_3512_);
v___x_3514_ = lean_box(v_nondep_3487_);
v___x_3515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3515_, 0, v___y_3506_);
lean_ctor_set(v___x_3515_, 1, v___x_3514_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set_tag(v___x_3495_, 1);
lean_ctor_set(v___x_3495_, 0, v___x_3515_);
v___x_3517_ = v___x_3495_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3515_);
v___x_3517_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
if (v___y_3503_ == 0)
{
lean_object* v___x_3518_; uint8_t v___x_3519_; 
v___x_3518_ = l_Lean_Expr_looseBVarRange(v_type_3484_);
lean_dec_ref(v_type_3484_);
v___x_3519_ = lean_nat_dec_le(v___x_3518_, v_cleanSuffix_3498_);
lean_dec(v___x_3518_);
if (v___x_3519_ == 0)
{
uint8_t v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = 1;
v___x_3521_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_declName_3483_, v_a_3493_, v___x_3517_, v___x_3520_, v___y_3510_, v___f_3513_, v___y_3500_, v___y_3505_, v___y_3508_, v___y_3501_, v___y_3502_, v___y_3509_, v___y_3504_, v___y_3507_);
return v___x_3521_;
}
else
{
lean_object* v___x_3522_; 
v___x_3522_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_declName_3483_, v_a_3493_, v___x_3517_, v___y_3503_, v___y_3510_, v___f_3513_, v___y_3500_, v___y_3505_, v___y_3508_, v___y_3501_, v___y_3502_, v___y_3509_, v___y_3504_, v___y_3507_);
return v___x_3522_;
}
}
else
{
lean_object* v___x_3523_; 
lean_dec_ref(v_type_3484_);
v___x_3523_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_declName_3483_, v_a_3493_, v___x_3517_, v___y_3503_, v___y_3510_, v___f_3513_, v___y_3500_, v___y_3505_, v___y_3508_, v___y_3501_, v___y_3502_, v___y_3509_, v___y_3504_, v___y_3507_);
return v___x_3523_;
}
}
}
v___jp_3525_:
{
lean_object* v___x_3534_; 
lean_inc(v_a_3491_);
v___x_3534_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3491_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
if (lean_obj_tag(v___x_3534_) == 0)
{
if (v_nondep_3487_ == 0)
{
lean_object* v_a_3535_; uint8_t v___x_3536_; uint8_t v___x_3537_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3535_);
lean_dec_ref_known(v___x_3534_, 1);
v___x_3536_ = 1;
v___x_3537_ = l_Lean_Expr_hasExprMVar(v_e_3346_);
if (v___x_3537_ == 0)
{
v___y_3500_ = v___y_3526_;
v___y_3501_ = v___y_3529_;
v___y_3502_ = v___y_3530_;
v___y_3503_ = v___x_3536_;
v___y_3504_ = v___y_3532_;
v___y_3505_ = v___y_3527_;
v___y_3506_ = v_a_3535_;
v___y_3507_ = v___y_3533_;
v___y_3508_ = v___y_3528_;
v___y_3509_ = v___y_3531_;
v___y_3510_ = v___x_3536_;
goto v___jp_3499_;
}
else
{
v___y_3500_ = v___y_3526_;
v___y_3501_ = v___y_3529_;
v___y_3502_ = v___y_3530_;
v___y_3503_ = v___x_3536_;
v___y_3504_ = v___y_3532_;
v___y_3505_ = v___y_3527_;
v___y_3506_ = v_a_3535_;
v___y_3507_ = v___y_3533_;
v___y_3508_ = v___y_3528_;
v___y_3509_ = v___y_3531_;
v___y_3510_ = v_nondep_3487_;
goto v___jp_3499_;
}
}
else
{
lean_object* v_a_3538_; uint8_t v___x_3539_; 
v_a_3538_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3538_);
lean_dec_ref_known(v___x_3534_, 1);
v___x_3539_ = 0;
v___y_3500_ = v___y_3526_;
v___y_3501_ = v___y_3529_;
v___y_3502_ = v___y_3530_;
v___y_3503_ = v___x_3539_;
v___y_3504_ = v___y_3532_;
v___y_3505_ = v___y_3527_;
v___y_3506_ = v_a_3538_;
v___y_3507_ = v___y_3533_;
v___y_3508_ = v___y_3528_;
v___y_3509_ = v___y_3531_;
v___y_3510_ = v___x_3539_;
goto v___jp_3499_;
}
}
else
{
lean_del_object(v___x_3495_);
lean_dec(v_a_3493_);
lean_dec(v_a_3491_);
lean_dec(v_a_3489_);
lean_dec_ref(v_body_3486_);
lean_dec_ref(v_value_3485_);
lean_dec_ref(v_type_3484_);
lean_dec(v_declName_3483_);
lean_dec_ref_known(v_e_3346_, 4);
return v___x_3534_;
}
}
}
}
else
{
lean_dec(v_a_3491_);
lean_dec(v_a_3489_);
lean_dec_ref(v_body_3486_);
lean_dec_ref(v_value_3485_);
lean_dec_ref(v_type_3484_);
lean_dec_ref_known(v_e_3346_, 4);
lean_dec(v_declName_3483_);
return v___x_3492_;
}
}
else
{
lean_dec(v_a_3489_);
lean_dec_ref(v_body_3486_);
lean_dec_ref(v_value_3485_);
lean_dec_ref(v_type_3484_);
lean_dec_ref_known(v_e_3346_, 4);
lean_dec(v_declName_3483_);
return v___x_3490_;
}
}
else
{
lean_dec_ref(v_body_3486_);
lean_dec_ref(v_value_3485_);
lean_dec_ref(v_type_3484_);
lean_dec_ref_known(v_e_3346_, 4);
lean_dec(v_declName_3483_);
return v___x_3488_;
}
}
default: 
{
lean_object* v___x_3578_; lean_object* v___x_3579_; 
lean_dec_ref(v_e_3346_);
v___x_3578_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1);
v___x_3579_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(v___x_3578_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
return v___x_3579_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(lean_object* v_e_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_){
_start:
{
lean_object* v___x_3589_; lean_object* v_visitedClosed_3590_; lean_object* v___x_3591_; 
v___x_3589_ = lean_st_ref_get(v_a_3581_);
v_visitedClosed_3590_ = lean_ctor_get(v___x_3589_, 3);
lean_inc_ref(v_visitedClosed_3590_);
lean_dec(v___x_3589_);
v___x_3591_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_visitedClosed_3590_, v_e_3580_);
lean_dec_ref(v_visitedClosed_3590_);
if (lean_obj_tag(v___x_3591_) == 1)
{
lean_object* v_val_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
lean_dec_ref(v_e_3580_);
v_val_3592_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3591_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_val_3592_);
lean_dec(v___x_3591_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
lean_ctor_set_tag(v___x_3594_, 0);
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_val_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
else
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v_visited_3602_; lean_object* v_types_3603_; lean_object* v_subst_3604_; lean_object* v_visitedClosed_3605_; lean_object* v_hasDepLetCache_3606_; lean_object* v_numConverted_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3677_; 
lean_dec(v___x_3591_);
v___x_3600_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2);
v___x_3601_ = lean_st_ref_take(v_a_3581_);
v_visited_3602_ = lean_ctor_get(v___x_3601_, 0);
v_types_3603_ = lean_ctor_get(v___x_3601_, 1);
v_subst_3604_ = lean_ctor_get(v___x_3601_, 2);
v_visitedClosed_3605_ = lean_ctor_get(v___x_3601_, 3);
v_hasDepLetCache_3606_ = lean_ctor_get(v___x_3601_, 4);
v_numConverted_3607_ = lean_ctor_get(v___x_3601_, 5);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3609_ = v___x_3601_;
v_isShared_3610_ = v_isSharedCheck_3677_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_numConverted_3607_);
lean_inc(v_hasDepLetCache_3606_);
lean_inc(v_visitedClosed_3605_);
lean_inc(v_subst_3604_);
lean_inc(v_types_3603_);
lean_inc(v_visited_3602_);
lean_dec(v___x_3601_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3677_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3611_; lean_object* v___x_3613_; 
v___x_3611_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 2, v___x_3611_);
lean_ctor_set(v___x_3609_, 1, v___x_3611_);
lean_ctor_set(v___x_3609_, 0, v___x_3611_);
v___x_3613_ = v___x_3609_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3611_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v___x_3611_);
lean_ctor_set(v_reuseFailAlloc_3676_, 2, v___x_3611_);
lean_ctor_set(v_reuseFailAlloc_3676_, 3, v_visitedClosed_3605_);
lean_ctor_set(v_reuseFailAlloc_3676_, 4, v_hasDepLetCache_3606_);
lean_ctor_set(v_reuseFailAlloc_3676_, 5, v_numConverted_3607_);
v___x_3613_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___x_3614_; lean_object* v_r_3615_; 
v___x_3614_ = lean_st_ref_put(v_a_3581_, v___x_3613_);
lean_inc_ref(v_e_3580_);
v_r_3615_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(v_e_3580_, v___x_3600_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_);
if (lean_obj_tag(v_r_3615_) == 0)
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3656_; 
v_a_3616_ = lean_ctor_get(v_r_3615_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v_r_3615_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3618_ = v_r_3615_;
v_isShared_3619_ = v_isSharedCheck_3656_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v_r_3615_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3656_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
lean_inc(v_a_3616_);
if (v_isShared_3619_ == 0)
{
lean_ctor_set_tag(v___x_3618_, 1);
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_a_3616_);
v___x_3621_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
lean_object* v___x_3622_; 
v___x_3622_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(v_a_3581_, v_visited_3602_, v_types_3603_, v_subst_3604_, v___x_3621_);
lean_dec_ref(v___x_3621_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3645_; 
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3645_ == 0)
{
lean_object* v_unused_3646_; 
v_unused_3646_ = lean_ctor_get(v___x_3622_, 0);
lean_dec(v_unused_3646_);
v___x_3624_ = v___x_3622_;
v_isShared_3625_ = v_isSharedCheck_3645_;
goto v_resetjp_3623_;
}
else
{
lean_dec(v___x_3622_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3645_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3626_; lean_object* v_visited_3627_; lean_object* v_types_3628_; lean_object* v_subst_3629_; lean_object* v_visitedClosed_3630_; lean_object* v_hasDepLetCache_3631_; lean_object* v_numConverted_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3644_; 
v___x_3626_ = lean_st_ref_take(v_a_3581_);
v_visited_3627_ = lean_ctor_get(v___x_3626_, 0);
v_types_3628_ = lean_ctor_get(v___x_3626_, 1);
v_subst_3629_ = lean_ctor_get(v___x_3626_, 2);
v_visitedClosed_3630_ = lean_ctor_get(v___x_3626_, 3);
v_hasDepLetCache_3631_ = lean_ctor_get(v___x_3626_, 4);
v_numConverted_3632_ = lean_ctor_get(v___x_3626_, 5);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3634_ = v___x_3626_;
v_isShared_3635_ = v_isSharedCheck_3644_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_numConverted_3632_);
lean_inc(v_hasDepLetCache_3631_);
lean_inc(v_visitedClosed_3630_);
lean_inc(v_subst_3629_);
lean_inc(v_types_3628_);
lean_inc(v_visited_3627_);
lean_dec(v___x_3626_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3644_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3636_; lean_object* v___x_3638_; 
lean_inc(v_a_3616_);
v___x_3636_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_visitedClosed_3630_, v_e_3580_, v_a_3616_);
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 3, v___x_3636_);
v___x_3638_ = v___x_3634_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_visited_3627_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v_types_3628_);
lean_ctor_set(v_reuseFailAlloc_3643_, 2, v_subst_3629_);
lean_ctor_set(v_reuseFailAlloc_3643_, 3, v___x_3636_);
lean_ctor_set(v_reuseFailAlloc_3643_, 4, v_hasDepLetCache_3631_);
lean_ctor_set(v_reuseFailAlloc_3643_, 5, v_numConverted_3632_);
v___x_3638_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
lean_object* v___x_3639_; lean_object* v___x_3641_; 
v___x_3639_ = lean_st_ref_put(v_a_3581_, v___x_3638_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 0, v_a_3616_);
v___x_3641_ = v___x_3624_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3616_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
}
}
else
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3654_; 
lean_dec(v_a_3616_);
lean_dec_ref(v_e_3580_);
v_a_3647_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3649_ = v___x_3622_;
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v___x_3622_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3652_; 
if (v_isShared_3650_ == 0)
{
v___x_3652_ = v___x_3649_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_a_3647_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
}
}
}
}
else
{
lean_object* v_a_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
lean_dec_ref(v_e_3580_);
v_a_3657_ = lean_ctor_get(v_r_3615_, 0);
lean_inc(v_a_3657_);
lean_dec_ref_known(v_r_3615_, 1);
v___x_3658_ = lean_box(0);
v___x_3659_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(v_a_3581_, v_visited_3602_, v_types_3603_, v_subst_3604_, v___x_3658_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3666_ == 0)
{
lean_object* v_unused_3667_; 
v_unused_3667_ = lean_ctor_get(v___x_3659_, 0);
lean_dec(v_unused_3667_);
v___x_3661_ = v___x_3659_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_dec(v___x_3659_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
lean_ctor_set_tag(v___x_3661_, 1);
lean_ctor_set(v___x_3661_, 0, v_a_3657_);
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3657_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
lean_dec(v_a_3657_);
v_a_3668_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3659_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3659_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3668_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(lean_object* v_e_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_){
_start:
{
lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; 
switch(lean_obj_tag(v_e_3678_))
{
case 0:
{
lean_object* v___x_3754_; 
v___x_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3754_, 0, v_e_3678_);
return v___x_3754_;
}
case 1:
{
lean_object* v___x_3755_; 
v___x_3755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3755_, 0, v_e_3678_);
return v___x_3755_;
}
case 2:
{
lean_object* v___x_3756_; 
v___x_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3756_, 0, v_e_3678_);
return v___x_3756_;
}
case 3:
{
lean_object* v___x_3757_; 
v___x_3757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3757_, 0, v_e_3678_);
return v___x_3757_;
}
case 4:
{
lean_object* v___x_3758_; 
v___x_3758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3758_, 0, v_e_3678_);
return v___x_3758_;
}
case 9:
{
lean_object* v___x_3759_; 
v___x_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3759_, 0, v_e_3678_);
return v___x_3759_;
}
default: 
{
lean_object* v_numCandidates_3760_; lean_object* v_cleanSuffix_3761_; lean_object* v___x_3762_; uint8_t v___x_3763_; 
v_numCandidates_3760_ = lean_ctor_get(v_a_3679_, 1);
v_cleanSuffix_3761_ = lean_ctor_get(v_a_3679_, 2);
v___x_3762_ = lean_unsigned_to_nat(0u);
v___x_3763_ = lean_nat_dec_eq(v_numCandidates_3760_, v___x_3762_);
if (v___x_3763_ == 0)
{
lean_object* v___x_3764_; uint8_t v___x_3765_; 
v___x_3764_ = l_Lean_Expr_looseBVarRange(v_e_3678_);
v___x_3765_ = lean_nat_dec_le(v___x_3764_, v_cleanSuffix_3761_);
lean_dec(v___x_3764_);
if (v___x_3765_ == 0)
{
v___y_3689_ = v_a_3679_;
v___y_3690_ = v_a_3680_;
v___y_3691_ = v_a_3681_;
v___y_3692_ = v_a_3682_;
v___y_3693_ = v_a_3683_;
v___y_3694_ = v_a_3684_;
v___y_3695_ = v_a_3685_;
v___y_3696_ = v_a_3686_;
goto v___jp_3688_;
}
else
{
goto v___jp_3735_;
}
}
else
{
goto v___jp_3735_;
}
}
}
v___jp_3688_:
{
uint8_t v___x_3697_; 
v___x_3697_ = l_Lean_Expr_hasLooseBVars(v_e_3678_);
if (v___x_3697_ == 0)
{
lean_object* v___x_3698_; 
v___x_3698_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(v_e_3678_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_);
return v___x_3698_;
}
else
{
lean_object* v___x_3699_; lean_object* v_visited_3700_; lean_object* v___x_3701_; 
v___x_3699_ = lean_st_ref_get(v___y_3690_);
v_visited_3700_ = lean_ctor_get(v___x_3699_, 0);
lean_inc_ref(v_visited_3700_);
lean_dec(v___x_3699_);
v___x_3701_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_visited_3700_, v_e_3678_);
lean_dec_ref(v_visited_3700_);
if (lean_obj_tag(v___x_3701_) == 1)
{
lean_object* v_val_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3709_; 
lean_dec_ref(v_e_3678_);
v_val_3702_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3704_ = v___x_3701_;
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_val_3702_);
lean_dec(v___x_3701_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3707_; 
if (v_isShared_3705_ == 0)
{
lean_ctor_set_tag(v___x_3704_, 0);
v___x_3707_ = v___x_3704_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_val_3702_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
else
{
lean_object* v___x_3710_; 
lean_dec(v___x_3701_);
lean_inc_ref(v_e_3678_);
v___x_3710_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(v_e_3678_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3734_; 
v_a_3711_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3713_ = v___x_3710_;
v_isShared_3714_ = v_isSharedCheck_3734_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3710_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3734_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3715_; lean_object* v_visited_3716_; lean_object* v_types_3717_; lean_object* v_subst_3718_; lean_object* v_visitedClosed_3719_; lean_object* v_hasDepLetCache_3720_; lean_object* v_numConverted_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3733_; 
v___x_3715_ = lean_st_ref_take(v___y_3690_);
v_visited_3716_ = lean_ctor_get(v___x_3715_, 0);
v_types_3717_ = lean_ctor_get(v___x_3715_, 1);
v_subst_3718_ = lean_ctor_get(v___x_3715_, 2);
v_visitedClosed_3719_ = lean_ctor_get(v___x_3715_, 3);
v_hasDepLetCache_3720_ = lean_ctor_get(v___x_3715_, 4);
v_numConverted_3721_ = lean_ctor_get(v___x_3715_, 5);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3723_ = v___x_3715_;
v_isShared_3724_ = v_isSharedCheck_3733_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_numConverted_3721_);
lean_inc(v_hasDepLetCache_3720_);
lean_inc(v_visitedClosed_3719_);
lean_inc(v_subst_3718_);
lean_inc(v_types_3717_);
lean_inc(v_visited_3716_);
lean_dec(v___x_3715_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3733_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3725_; lean_object* v___x_3727_; 
lean_inc(v_a_3711_);
v___x_3725_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_visited_3716_, v_e_3678_, v_a_3711_);
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 0, v___x_3725_);
v___x_3727_ = v___x_3723_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3725_);
lean_ctor_set(v_reuseFailAlloc_3732_, 1, v_types_3717_);
lean_ctor_set(v_reuseFailAlloc_3732_, 2, v_subst_3718_);
lean_ctor_set(v_reuseFailAlloc_3732_, 3, v_visitedClosed_3719_);
lean_ctor_set(v_reuseFailAlloc_3732_, 4, v_hasDepLetCache_3720_);
lean_ctor_set(v_reuseFailAlloc_3732_, 5, v_numConverted_3721_);
v___x_3727_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
lean_object* v___x_3728_; lean_object* v___x_3730_; 
v___x_3728_ = lean_st_ref_put(v___y_3690_, v___x_3727_);
if (v_isShared_3714_ == 0)
{
v___x_3730_ = v___x_3713_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3711_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3678_);
return v___x_3710_;
}
}
}
}
v___jp_3735_:
{
lean_object* v___x_3736_; 
lean_inc_ref(v_e_3678_);
v___x_3736_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_e_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3745_; 
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3739_ = v___x_3736_;
v_isShared_3740_ = v_isSharedCheck_3745_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3736_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3745_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
uint8_t v___x_3741_; 
v___x_3741_ = lean_unbox(v_a_3737_);
lean_dec(v_a_3737_);
if (v___x_3741_ == 0)
{
lean_object* v___x_3743_; 
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 0, v_e_3678_);
v___x_3743_ = v___x_3739_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_e_3678_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
else
{
lean_del_object(v___x_3739_);
v___y_3689_ = v_a_3679_;
v___y_3690_ = v_a_3680_;
v___y_3691_ = v_a_3681_;
v___y_3692_ = v_a_3682_;
v___y_3693_ = v_a_3683_;
v___y_3694_ = v_a_3684_;
v___y_3695_ = v_a_3685_;
v___y_3696_ = v_a_3686_;
goto v___jp_3688_;
}
}
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_dec_ref(v_e_3678_);
v_a_3746_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3736_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3736_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0(lean_object* v_body_3766_, lean_object* v_binderType_3767_, lean_object* v_a_3768_, lean_object* v_binderName_3769_, uint8_t v_binderInfo_3770_, lean_object* v_e_3771_, lean_object* v_x_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v___x_3782_; 
lean_inc_ref(v_body_3766_);
v___x_3782_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_body_3766_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3798_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3785_ = v___x_3782_;
v_isShared_3786_ = v_isSharedCheck_3798_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3782_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3798_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
size_t v___x_3787_; size_t v___x_3788_; uint8_t v___x_3789_; 
v___x_3787_ = lean_ptr_addr(v_binderType_3767_);
v___x_3788_ = lean_ptr_addr(v_a_3768_);
v___x_3789_ = lean_usize_dec_eq(v___x_3787_, v___x_3788_);
if (v___x_3789_ == 0)
{
lean_object* v___x_3790_; 
lean_del_object(v___x_3785_);
lean_dec_ref(v_e_3771_);
lean_dec_ref(v_body_3766_);
v___x_3790_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(v_binderName_3769_, v_binderInfo_3770_, v_a_3768_, v_a_3783_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
return v___x_3790_;
}
else
{
size_t v___x_3791_; size_t v___x_3792_; uint8_t v___x_3793_; 
v___x_3791_ = lean_ptr_addr(v_body_3766_);
lean_dec_ref(v_body_3766_);
v___x_3792_ = lean_ptr_addr(v_a_3783_);
v___x_3793_ = lean_usize_dec_eq(v___x_3791_, v___x_3792_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3794_; 
lean_del_object(v___x_3785_);
lean_dec_ref(v_e_3771_);
v___x_3794_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(v_binderName_3769_, v_binderInfo_3770_, v_a_3768_, v_a_3783_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
return v___x_3794_;
}
else
{
lean_object* v___x_3796_; 
lean_dec(v_a_3783_);
lean_dec(v_binderName_3769_);
lean_dec_ref(v_a_3768_);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 0, v_e_3771_);
v___x_3796_ = v___x_3785_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_e_3771_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3771_);
lean_dec(v_binderName_3769_);
lean_dec_ref(v_a_3768_);
lean_dec_ref(v_body_3766_);
return v___x_3782_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___boxed(lean_object* v_e_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_){
_start:
{
lean_object* v_res_3809_; 
v_res_3809_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(v_e_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
lean_dec(v_a_3807_);
lean_dec_ref(v_a_3806_);
lean_dec(v_a_3805_);
lean_dec_ref(v_a_3804_);
lean_dec(v_a_3803_);
lean_dec_ref(v_a_3802_);
lean_dec(v_a_3801_);
lean_dec_ref(v_a_3800_);
return v_res_3809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___boxed(lean_object* v_e_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_){
_start:
{
lean_object* v_res_3819_; 
v_res_3819_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(v_e_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
lean_dec(v_a_3817_);
lean_dec_ref(v_a_3816_);
lean_dec(v_a_3815_);
lean_dec_ref(v_a_3814_);
lean_dec(v_a_3813_);
lean_dec_ref(v_a_3812_);
lean_dec(v_a_3811_);
return v_res_3819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit___boxed(lean_object* v_e_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_e_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_);
lean_dec(v_a_3828_);
lean_dec_ref(v_a_3827_);
lean_dec(v_a_3826_);
lean_dec_ref(v_a_3825_);
lean_dec(v_a_3824_);
lean_dec_ref(v_a_3823_);
lean_dec(v_a_3822_);
lean_dec_ref(v_a_3821_);
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___boxed(lean_object* v_e_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_){
_start:
{
lean_object* v_res_3841_; 
v_res_3841_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(v_e_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_);
lean_dec(v_a_3839_);
lean_dec_ref(v_a_3838_);
lean_dec(v_a_3837_);
lean_dec_ref(v_a_3836_);
lean_dec(v_a_3835_);
lean_dec_ref(v_a_3834_);
lean_dec(v_a_3833_);
lean_dec_ref(v_a_3832_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1(lean_object* v_f_3842_, lean_object* v_a_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
lean_object* v___x_3853_; 
v___x_3853_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(v_f_3842_, v_a_3843_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___boxed(lean_object* v_f_3854_, lean_object* v_a_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1(v_f_3854_, v_a_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2(lean_object* v_d_3866_, lean_object* v_e_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v___x_3877_; 
v___x_3877_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(v_d_3866_, v_e_3867_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___boxed(lean_object* v_d_3878_, lean_object* v_e_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_){
_start:
{
lean_object* v_res_3889_; 
v_res_3889_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2(v_d_3878_, v_e_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
return v_res_3889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3(lean_object* v_structName_3890_, lean_object* v_idx_3891_, lean_object* v_struct_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v___x_3902_; 
v___x_3902_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(v_structName_3890_, v_idx_3891_, v_struct_3892_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___boxed(lean_object* v_structName_3903_, lean_object* v_idx_3904_, lean_object* v_struct_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3(v_structName_3903_, v_idx_3904_, v_struct_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
lean_dec(v___y_3913_);
lean_dec_ref(v___y_3912_);
lean_dec(v___y_3911_);
lean_dec_ref(v___y_3910_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4(lean_object* v_x_3916_, uint8_t v_bi_3917_, lean_object* v_t_3918_, lean_object* v_b_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
lean_object* v___x_3929_; 
v___x_3929_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(v_x_3916_, v_bi_3917_, v_t_3918_, v_b_3919_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___boxed(lean_object* v_x_3930_, lean_object* v_bi_3931_, lean_object* v_t_3932_, lean_object* v_b_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
uint8_t v_bi_boxed_3943_; lean_object* v_res_3944_; 
v_bi_boxed_3943_ = lean_unbox(v_bi_3931_);
v_res_3944_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4(v_x_3930_, v_bi_boxed_3943_, v_t_3932_, v_b_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec(v___y_3935_);
lean_dec_ref(v___y_3934_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5(lean_object* v_x_3945_, lean_object* v_t_3946_, lean_object* v_v_3947_, lean_object* v_b_3948_, uint8_t v_nondep_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v___x_3959_; 
v___x_3959_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_x_3945_, v_t_3946_, v_v_3947_, v_b_3948_, v_nondep_3949_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___boxed(lean_object* v_x_3960_, lean_object* v_t_3961_, lean_object* v_v_3962_, lean_object* v_b_3963_, lean_object* v_nondep_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_){
_start:
{
uint8_t v_nondep_boxed_3974_; lean_object* v_res_3975_; 
v_nondep_boxed_3974_ = lean_unbox(v_nondep_3964_);
v_res_3975_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5(v_x_3960_, v_t_3961_, v_v_3962_, v_b_3963_, v_nondep_boxed_3974_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8(lean_object* v_x_3976_, uint8_t v_bi_3977_, lean_object* v_t_3978_, lean_object* v_b_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v___x_3989_; 
v___x_3989_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(v_x_3976_, v_bi_3977_, v_t_3978_, v_b_3979_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___boxed(lean_object* v_x_3990_, lean_object* v_bi_3991_, lean_object* v_t_3992_, lean_object* v_b_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_){
_start:
{
uint8_t v_bi_boxed_4003_; lean_object* v_res_4004_; 
v_bi_boxed_4003_ = lean_unbox(v_bi_3991_);
v_res_4004_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8(v_x_3990_, v_bi_boxed_4003_, v_t_3992_, v_b_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_);
lean_dec(v___y_4001_);
lean_dec_ref(v___y_4000_);
lean_dec(v___y_3999_);
lean_dec_ref(v___y_3998_);
lean_dec(v___y_3997_);
lean_dec_ref(v___y_3996_);
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
return v_res_4004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed(lean_object* v_e_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_){
_start:
{
lean_object* v___x_4015_; 
v___x_4015_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(v_e_4005_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___boxed(lean_object* v_e_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed(v_e_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_);
lean_dec(v_a_4024_);
lean_dec_ref(v_a_4023_);
lean_dec(v_a_4022_);
lean_dec_ref(v_a_4021_);
lean_dec(v_a_4020_);
lean_dec_ref(v_a_4019_);
lean_dec(v_a_4018_);
lean_dec_ref(v_a_4017_);
return v_res_4026_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6(lean_object* v_00_u03b2_4027_, lean_object* v_k_4028_, lean_object* v_t_4029_){
_start:
{
uint8_t v___x_4030_; 
v___x_4030_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(v_k_4028_, v_t_4029_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___boxed(lean_object* v_00_u03b2_4031_, lean_object* v_k_4032_, lean_object* v_t_4033_){
_start:
{
uint8_t v_res_4034_; lean_object* v_r_4035_; 
v_res_4034_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6(v_00_u03b2_4031_, v_k_4032_, v_t_4033_);
lean_dec(v_t_4033_);
lean_dec(v_k_4032_);
v_r_4035_ = lean_box(v_res_4034_);
return v_r_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0(lean_object* v_x_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_){
_start:
{
lean_object* v___x_4044_; 
lean_inc(v___y_4038_);
lean_inc_ref(v___y_4037_);
v___x_4044_ = lean_apply_7(v_x_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, lean_box(0));
return v___x_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0___boxed(lean_object* v_x_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0(v_x_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(lean_object* v_lctx_4054_, lean_object* v_localInsts_4055_, lean_object* v_x_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_){
_start:
{
lean_object* v___f_4064_; lean_object* v___x_4065_; 
lean_inc(v___y_4058_);
lean_inc_ref(v___y_4057_);
v___f_4064_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4064_, 0, v_x_4056_);
lean_closure_set(v___f_4064_, 1, v___y_4057_);
lean_closure_set(v___f_4064_, 2, v___y_4058_);
v___x_4065_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4054_, v_localInsts_4055_, v___f_4064_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
if (lean_obj_tag(v___x_4065_) == 0)
{
return v___x_4065_;
}
else
{
lean_object* v_a_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4073_; 
v_a_4066_ = lean_ctor_get(v___x_4065_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v___x_4065_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4068_ = v___x_4065_;
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_a_4066_);
lean_dec(v___x_4065_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4071_; 
if (v_isShared_4069_ == 0)
{
v___x_4071_ = v___x_4068_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_a_4066_);
v___x_4071_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
return v___x_4071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___boxed(lean_object* v_lctx_4074_, lean_object* v_localInsts_4075_, lean_object* v_x_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(v_lctx_4074_, v_localInsts_4075_, v_x_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0(lean_object* v_00_u03b1_4085_, lean_object* v_lctx_4086_, lean_object* v_localInsts_4087_, lean_object* v_x_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
lean_object* v___x_4096_; 
v___x_4096_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(v_lctx_4086_, v_localInsts_4087_, v_x_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___boxed(lean_object* v_00_u03b1_4097_, lean_object* v_lctx_4098_, lean_object* v_localInsts_4099_, lean_object* v_x_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0(v_00_u03b1_4097_, v_lctx_4098_, v_localInsts_4099_, v_x_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
return v_res_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0(lean_object* v_k_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v___x_4117_; 
lean_inc(v___y_4111_);
lean_inc_ref(v___y_4110_);
v___x_4117_ = lean_apply_7(v_k_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, lean_box(0));
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0___boxed(lean_object* v_k_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0(v_k_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg(lean_object* v_k_4127_, uint8_t v_allowLevelAssignments_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_){
_start:
{
lean_object* v___f_4136_; lean_object* v___x_4137_; 
lean_inc(v___y_4130_);
lean_inc_ref(v___y_4129_);
v___f_4136_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4136_, 0, v_k_4127_);
lean_closure_set(v___f_4136_, 1, v___y_4129_);
lean_closure_set(v___f_4136_, 2, v___y_4130_);
v___x_4137_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_4128_, v___f_4136_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
if (lean_obj_tag(v___x_4137_) == 0)
{
return v___x_4137_;
}
else
{
lean_object* v_a_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4145_; 
v_a_4138_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4140_ = v___x_4137_;
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_a_4138_);
lean_dec(v___x_4137_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4143_; 
if (v_isShared_4141_ == 0)
{
v___x_4143_ = v___x_4140_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4138_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___boxed(lean_object* v_k_4146_, lean_object* v_allowLevelAssignments_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_4155_; lean_object* v_res_4156_; 
v_allowLevelAssignments_boxed_4155_ = lean_unbox(v_allowLevelAssignments_4147_);
v_res_4156_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg(v_k_4146_, v_allowLevelAssignments_boxed_4155_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
return v_res_4156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1(lean_object* v_00_u03b1_4157_, lean_object* v_k_4158_, uint8_t v_allowLevelAssignments_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_){
_start:
{
lean_object* v___x_4167_; 
v___x_4167_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg(v_k_4158_, v_allowLevelAssignments_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_);
return v___x_4167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___boxed(lean_object* v_00_u03b1_4168_, lean_object* v_k_4169_, lean_object* v_allowLevelAssignments_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_4178_; lean_object* v_res_4179_; 
v_allowLevelAssignments_boxed_4178_ = lean_unbox(v_allowLevelAssignments_4170_);
v_res_4179_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1(v_00_u03b1_4168_, v_k_4169_, v_allowLevelAssignments_boxed_4178_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__0(lean_object* v_cfg_4180_){
_start:
{
uint8_t v_foApprox_4181_; uint8_t v_ctxApprox_4182_; uint8_t v_quasiPatternApprox_4183_; uint8_t v_constApprox_4184_; uint8_t v_isDefEqStuckEx_4185_; uint8_t v_unificationHints_4186_; uint8_t v_proofIrrelevance_4187_; uint8_t v_assignSyntheticOpaque_4188_; uint8_t v_offsetCnstrs_4189_; uint8_t v_transparency_4190_; uint8_t v_univApprox_4191_; uint8_t v_zetaUnused_4192_; uint8_t v_canUnfoldPredicateConfig_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4203_; 
v_foApprox_4181_ = lean_ctor_get_uint8(v_cfg_4180_, 0);
v_ctxApprox_4182_ = lean_ctor_get_uint8(v_cfg_4180_, 1);
v_quasiPatternApprox_4183_ = lean_ctor_get_uint8(v_cfg_4180_, 2);
v_constApprox_4184_ = lean_ctor_get_uint8(v_cfg_4180_, 3);
v_isDefEqStuckEx_4185_ = lean_ctor_get_uint8(v_cfg_4180_, 4);
v_unificationHints_4186_ = lean_ctor_get_uint8(v_cfg_4180_, 5);
v_proofIrrelevance_4187_ = lean_ctor_get_uint8(v_cfg_4180_, 6);
v_assignSyntheticOpaque_4188_ = lean_ctor_get_uint8(v_cfg_4180_, 7);
v_offsetCnstrs_4189_ = lean_ctor_get_uint8(v_cfg_4180_, 8);
v_transparency_4190_ = lean_ctor_get_uint8(v_cfg_4180_, 9);
v_univApprox_4191_ = lean_ctor_get_uint8(v_cfg_4180_, 11);
v_zetaUnused_4192_ = lean_ctor_get_uint8(v_cfg_4180_, 17);
v_canUnfoldPredicateConfig_4193_ = lean_ctor_get_uint8(v_cfg_4180_, 19);
v_isSharedCheck_4203_ = !lean_is_exclusive(v_cfg_4180_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4195_ = v_cfg_4180_;
v_isShared_4196_ = v_isSharedCheck_4203_;
goto v_resetjp_4194_;
}
else
{
lean_dec(v_cfg_4180_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4203_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
uint8_t v___x_4197_; uint8_t v___x_4198_; uint8_t v___x_4199_; lean_object* v___x_4201_; 
v___x_4197_ = 0;
v___x_4198_ = 1;
v___x_4199_ = 2;
if (v_isShared_4196_ == 0)
{
v___x_4201_ = v___x_4195_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4202_, 0, v_foApprox_4181_);
lean_ctor_set_uint8(v_reuseFailAlloc_4202_, 1, v_ctxApprox_4182_);
lean_ctor_set_uint8(v_reuseFailAlloc_4202_, 2, v_quasiPatternApprox_4183_);
lean_ctor_set_uint8(v_reuseFailAlloc_4202_, 3, v_constApprox_4184_);
lean_ctor_set_uint8(v_reuseFailAlloc_4202_, 4, v_isDefEqStuckEx_4185_);
lean_ctor_set_uint8(v_reuseFailAlloc_4202_, 5, v_unificationHints_4186_);
lean_ctor_set_uint8(v_reuseFailAlloc_4202_, 6, v_proofIrrelevance_4187_);
lean_ctor_set_uint8(v_reuseFailAlloc_4202_, 7, v_assignSyntheticOpaque_4188_);
lean_ctor_set_uint8(v_reuseFailAlloc_4202_, 8, v_offsetCnstrs_4189_);
lean_ctor_set_uint8(v_reuseFailAlloc_4202_, 9, v_transparency_4190_);
lean_ctor_set_uint8(v_reuseFailAlloc_4202_, 11, v_univApprox_4191_);
lean_ctor_set_uint8(v_reuseFailAlloc_4202_, 17, v_zetaUnused_4192_);
lean_ctor_set_uint8(v_reuseFailAlloc_4202_, 19, v_canUnfoldPredicateConfig_4193_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
lean_ctor_set_uint8(v___x_4201_, 10, v___x_4197_);
lean_ctor_set_uint8(v___x_4201_, 12, v___x_4198_);
lean_ctor_set_uint8(v___x_4201_, 13, v___x_4198_);
lean_ctor_set_uint8(v___x_4201_, 14, v___x_4199_);
lean_ctor_set_uint8(v___x_4201_, 15, v___x_4198_);
lean_ctor_set_uint8(v___x_4201_, 16, v___x_4198_);
lean_ctor_set_uint8(v___x_4201_, 18, v___x_4198_);
return v___x_4201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__1(lean_object* v___x_4204_, lean_object* v_e_4205_, lean_object* v___x_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_){
_start:
{
lean_object* v___x_4214_; lean_object* v_a_4216_; lean_object* v___x_4219_; 
v___x_4214_ = lean_st_mk_ref(v___x_4204_);
lean_inc_ref(v_e_4205_);
v___x_4219_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_e_4205_, v___x_4206_, v___x_4214_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_object* v_a_4220_; uint8_t v___x_4221_; 
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
lean_inc(v_a_4220_);
lean_dec_ref_known(v___x_4219_, 1);
v___x_4221_ = lean_unbox(v_a_4220_);
lean_dec(v_a_4220_);
if (v___x_4221_ == 0)
{
v_a_4216_ = v_e_4205_;
goto v___jp_4215_;
}
else
{
lean_object* v___x_4222_; 
v___x_4222_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_e_4205_, v___x_4206_, v___x_4214_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v_a_4223_; 
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
lean_inc(v_a_4223_);
lean_dec_ref_known(v___x_4222_, 1);
v_a_4216_ = v_a_4223_;
goto v___jp_4215_;
}
else
{
lean_dec(v___x_4214_);
return v___x_4222_;
}
}
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
lean_dec(v___x_4214_);
lean_dec_ref(v_e_4205_);
v_a_4224_ = lean_ctor_get(v___x_4219_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4219_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4219_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4229_; 
if (v_isShared_4227_ == 0)
{
v___x_4229_ = v___x_4226_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
v___jp_4215_:
{
lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4217_ = lean_st_ref_get(v___x_4214_);
lean_dec(v___x_4214_);
lean_dec(v___x_4217_);
v___x_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4218_, 0, v_a_4216_);
return v___x_4218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__1___boxed(lean_object* v___x_4232_, lean_object* v_e_4233_, lean_object* v___x_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l_Lean_Meta_Sym_letToHave___lam__1(v___x_4232_, v_e_4233_, v___x_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_);
lean_dec(v___y_4240_);
lean_dec_ref(v___y_4239_);
lean_dec(v___y_4238_);
lean_dec_ref(v___y_4237_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
lean_dec_ref(v___x_4234_);
return v_res_4242_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___lam__2___closed__0(void){
_start:
{
lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v___x_4243_ = lean_unsigned_to_nat(0u);
v___x_4244_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1);
v___x_4245_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4244_);
lean_ctor_set(v___x_4245_, 1, v___x_4244_);
lean_ctor_set(v___x_4245_, 2, v___x_4244_);
lean_ctor_set(v___x_4245_, 3, v___x_4244_);
lean_ctor_set(v___x_4245_, 4, v___x_4244_);
lean_ctor_set(v___x_4245_, 5, v___x_4243_);
return v___x_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__2(lean_object* v_e_4246_, lean_object* v_____do__lift_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_){
_start:
{
lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___f_4258_; lean_object* v___x_4259_; 
v___x_4255_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___closed__0));
v___x_4256_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2);
v___x_4257_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__2___closed__0, &l_Lean_Meta_Sym_letToHave___lam__2___closed__0_once, _init_l_Lean_Meta_Sym_letToHave___lam__2___closed__0);
v___f_4258_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_letToHave___lam__1___boxed), 10, 3);
lean_closure_set(v___f_4258_, 0, v___x_4257_);
lean_closure_set(v___f_4258_, 1, v_e_4246_);
lean_closure_set(v___f_4258_, 2, v___x_4256_);
v___x_4259_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(v_____do__lift_4247_, v___x_4255_, v___f_4258_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
return v___x_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__2___boxed(lean_object* v_e_4260_, lean_object* v_____do__lift_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l_Lean_Meta_Sym_letToHave___lam__2(v_e_4260_, v_____do__lift_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec(v___y_4263_);
lean_dec_ref(v___y_4262_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__3(lean_object* v___y_4270_, lean_object* v_cache_4271_, lean_object* v_a_x3f_4272_){
_start:
{
lean_object* v___x_4274_; lean_object* v_mctx_4275_; lean_object* v_zetaDeltaFVarIds_4276_; lean_object* v_postponed_4277_; lean_object* v_diag_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4288_; 
v___x_4274_ = lean_st_ref_take(v___y_4270_);
v_mctx_4275_ = lean_ctor_get(v___x_4274_, 0);
v_zetaDeltaFVarIds_4276_ = lean_ctor_get(v___x_4274_, 2);
v_postponed_4277_ = lean_ctor_get(v___x_4274_, 3);
v_diag_4278_ = lean_ctor_get(v___x_4274_, 4);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4288_ == 0)
{
lean_object* v_unused_4289_; 
v_unused_4289_ = lean_ctor_get(v___x_4274_, 1);
lean_dec(v_unused_4289_);
v___x_4280_ = v___x_4274_;
v_isShared_4281_ = v_isSharedCheck_4288_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_diag_4278_);
lean_inc(v_postponed_4277_);
lean_inc(v_zetaDeltaFVarIds_4276_);
lean_inc(v_mctx_4275_);
lean_dec(v___x_4274_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4288_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4282_; lean_object* v___x_4284_; 
v___x_4282_ = lean_box(0);
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 1, v_cache_4271_);
v___x_4284_ = v___x_4280_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_mctx_4275_);
lean_ctor_set(v_reuseFailAlloc_4287_, 1, v_cache_4271_);
lean_ctor_set(v_reuseFailAlloc_4287_, 2, v_zetaDeltaFVarIds_4276_);
lean_ctor_set(v_reuseFailAlloc_4287_, 3, v_postponed_4277_);
lean_ctor_set(v_reuseFailAlloc_4287_, 4, v_diag_4278_);
v___x_4284_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; 
v___x_4285_ = lean_st_ref_put(v___y_4270_, v___x_4284_);
v___x_4286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4282_);
return v___x_4286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__3___boxed(lean_object* v___y_4290_, lean_object* v_cache_4291_, lean_object* v_a_x3f_4292_, lean_object* v___y_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l_Lean_Meta_Sym_letToHave___lam__3(v___y_4290_, v_cache_4291_, v_a_x3f_4292_);
lean_dec(v_a_x3f_4292_);
lean_dec(v___y_4290_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__4(lean_object* v___y_4295_, lean_object* v_zetaDeltaFVarIds_4296_, lean_object* v_a_x3f_4297_){
_start:
{
lean_object* v___x_4299_; lean_object* v_mctx_4300_; lean_object* v_cache_4301_; lean_object* v_postponed_4302_; lean_object* v_diag_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4313_; 
v___x_4299_ = lean_st_ref_take(v___y_4295_);
v_mctx_4300_ = lean_ctor_get(v___x_4299_, 0);
v_cache_4301_ = lean_ctor_get(v___x_4299_, 1);
v_postponed_4302_ = lean_ctor_get(v___x_4299_, 3);
v_diag_4303_ = lean_ctor_get(v___x_4299_, 4);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4313_ == 0)
{
lean_object* v_unused_4314_; 
v_unused_4314_ = lean_ctor_get(v___x_4299_, 2);
lean_dec(v_unused_4314_);
v___x_4305_ = v___x_4299_;
v_isShared_4306_ = v_isSharedCheck_4313_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_diag_4303_);
lean_inc(v_postponed_4302_);
lean_inc(v_cache_4301_);
lean_inc(v_mctx_4300_);
lean_dec(v___x_4299_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4313_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4307_; lean_object* v___x_4309_; 
v___x_4307_ = lean_box(0);
if (v_isShared_4306_ == 0)
{
lean_ctor_set(v___x_4305_, 2, v_zetaDeltaFVarIds_4296_);
v___x_4309_ = v___x_4305_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_mctx_4300_);
lean_ctor_set(v_reuseFailAlloc_4312_, 1, v_cache_4301_);
lean_ctor_set(v_reuseFailAlloc_4312_, 2, v_zetaDeltaFVarIds_4296_);
lean_ctor_set(v_reuseFailAlloc_4312_, 3, v_postponed_4302_);
lean_ctor_set(v_reuseFailAlloc_4312_, 4, v_diag_4303_);
v___x_4309_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
lean_object* v___x_4310_; lean_object* v___x_4311_; 
v___x_4310_ = lean_st_ref_put(v___y_4295_, v___x_4309_);
v___x_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4307_);
return v___x_4311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__4___boxed(lean_object* v___y_4315_, lean_object* v_zetaDeltaFVarIds_4316_, lean_object* v_a_x3f_4317_, lean_object* v___y_4318_){
_start:
{
lean_object* v_res_4319_; 
v_res_4319_ = l_Lean_Meta_Sym_letToHave___lam__4(v___y_4315_, v_zetaDeltaFVarIds_4316_, v_a_x3f_4317_);
lean_dec(v_a_x3f_4317_);
lean_dec(v___y_4315_);
return v_res_4319_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__0(void){
_start:
{
lean_object* v___x_4320_; 
v___x_4320_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4320_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__1(void){
_start:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; 
v___x_4321_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__5___closed__0, &l_Lean_Meta_Sym_letToHave___lam__5___closed__0_once, _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__0);
v___x_4322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4322_, 0, v___x_4321_);
return v___x_4322_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__2(void){
_start:
{
lean_object* v___x_4323_; lean_object* v___x_4324_; 
v___x_4323_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__5___closed__1, &l_Lean_Meta_Sym_letToHave___lam__5___closed__1_once, _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__1);
v___x_4324_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4323_);
lean_ctor_set(v___x_4324_, 1, v___x_4323_);
lean_ctor_set(v___x_4324_, 2, v___x_4323_);
lean_ctor_set(v___x_4324_, 3, v___x_4323_);
lean_ctor_set(v___x_4324_, 4, v___x_4323_);
lean_ctor_set(v___x_4324_, 5, v___x_4323_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__5(uint8_t v___x_4325_, lean_object* v___f_4326_, lean_object* v___f_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_){
_start:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v_cache_4337_; lean_object* v_a_4339_; lean_object* v___x_4350_; lean_object* v_mctx_4351_; lean_object* v_zetaDeltaFVarIds_4352_; lean_object* v_postponed_4353_; lean_object* v_diag_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4426_; 
v___x_4335_ = lean_box(1);
v___x_4336_ = lean_st_ref_get(v___y_4331_);
v_cache_4337_ = lean_ctor_get(v___x_4336_, 1);
lean_inc_ref(v_cache_4337_);
lean_dec(v___x_4336_);
v___x_4350_ = lean_st_ref_take(v___y_4331_);
v_mctx_4351_ = lean_ctor_get(v___x_4350_, 0);
v_zetaDeltaFVarIds_4352_ = lean_ctor_get(v___x_4350_, 2);
v_postponed_4353_ = lean_ctor_get(v___x_4350_, 3);
v_diag_4354_ = lean_ctor_get(v___x_4350_, 4);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4426_ == 0)
{
lean_object* v_unused_4427_; 
v_unused_4427_ = lean_ctor_get(v___x_4350_, 1);
lean_dec(v_unused_4427_);
v___x_4356_ = v___x_4350_;
v_isShared_4357_ = v_isSharedCheck_4426_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_diag_4354_);
lean_inc(v_postponed_4353_);
lean_inc(v_zetaDeltaFVarIds_4352_);
lean_inc(v_mctx_4351_);
lean_dec(v___x_4350_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4426_;
goto v_resetjp_4355_;
}
v___jp_4338_:
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4348_; 
v___x_4340_ = lean_box(0);
v___x_4341_ = l_Lean_Meta_Sym_letToHave___lam__3(v___y_4331_, v_cache_4337_, v___x_4340_);
v_isSharedCheck_4348_ = !lean_is_exclusive(v___x_4341_);
if (v_isSharedCheck_4348_ == 0)
{
lean_object* v_unused_4349_; 
v_unused_4349_ = lean_ctor_get(v___x_4341_, 0);
lean_dec(v_unused_4349_);
v___x_4343_ = v___x_4341_;
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
else
{
lean_dec(v___x_4341_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4346_; 
if (v_isShared_4344_ == 0)
{
lean_ctor_set_tag(v___x_4343_, 1);
lean_ctor_set(v___x_4343_, 0, v_a_4339_);
v___x_4346_ = v___x_4343_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_a_4339_);
v___x_4346_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
return v___x_4346_;
}
}
}
v_resetjp_4355_:
{
lean_object* v___x_4358_; lean_object* v___x_4360_; 
v___x_4358_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__5___closed__2, &l_Lean_Meta_Sym_letToHave___lam__5___closed__2_once, _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__2);
if (v_isShared_4357_ == 0)
{
lean_ctor_set(v___x_4356_, 1, v___x_4358_);
v___x_4360_ = v___x_4356_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_mctx_4351_);
lean_ctor_set(v_reuseFailAlloc_4425_, 1, v___x_4358_);
lean_ctor_set(v_reuseFailAlloc_4425_, 2, v_zetaDeltaFVarIds_4352_);
lean_ctor_set(v_reuseFailAlloc_4425_, 3, v_postponed_4353_);
lean_ctor_set(v_reuseFailAlloc_4425_, 4, v_diag_4354_);
v___x_4360_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
lean_object* v___x_4361_; lean_object* v_keyedConfig_4362_; lean_object* v_zetaDeltaSet_4363_; lean_object* v_lctx_4364_; lean_object* v_localInstances_4365_; lean_object* v_defEqCtx_x3f_4366_; lean_object* v_synthPendingDepth_4367_; lean_object* v_customCanUnfoldPredicate_x3f_4368_; uint8_t v_univApprox_4369_; uint8_t v_inTypeClassResolution_4370_; uint8_t v_cacheInferType_4371_; uint8_t v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v_mctx_4375_; lean_object* v_cache_4376_; lean_object* v_zetaDeltaFVarIds_4377_; lean_object* v_postponed_4378_; lean_object* v_diag_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4424_; 
v___x_4361_ = lean_st_ref_put(v___y_4331_, v___x_4360_);
v_keyedConfig_4362_ = lean_ctor_get(v___y_4330_, 0);
v_zetaDeltaSet_4363_ = lean_ctor_get(v___y_4330_, 1);
v_lctx_4364_ = lean_ctor_get(v___y_4330_, 2);
v_localInstances_4365_ = lean_ctor_get(v___y_4330_, 3);
v_defEqCtx_x3f_4366_ = lean_ctor_get(v___y_4330_, 4);
v_synthPendingDepth_4367_ = lean_ctor_get(v___y_4330_, 5);
v_customCanUnfoldPredicate_x3f_4368_ = lean_ctor_get(v___y_4330_, 6);
v_univApprox_4369_ = lean_ctor_get_uint8(v___y_4330_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4370_ = lean_ctor_get_uint8(v___y_4330_, sizeof(void*)*7 + 2);
v_cacheInferType_4371_ = lean_ctor_get_uint8(v___y_4330_, sizeof(void*)*7 + 3);
v___x_4372_ = 1;
lean_inc(v_customCanUnfoldPredicate_x3f_4368_);
lean_inc(v_synthPendingDepth_4367_);
lean_inc(v_defEqCtx_x3f_4366_);
lean_inc_ref(v_localInstances_4365_);
lean_inc_ref(v_lctx_4364_);
lean_inc(v_zetaDeltaSet_4363_);
lean_inc_ref(v_keyedConfig_4362_);
v___x_4373_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4373_, 0, v_keyedConfig_4362_);
lean_ctor_set(v___x_4373_, 1, v_zetaDeltaSet_4363_);
lean_ctor_set(v___x_4373_, 2, v_lctx_4364_);
lean_ctor_set(v___x_4373_, 3, v_localInstances_4365_);
lean_ctor_set(v___x_4373_, 4, v_defEqCtx_x3f_4366_);
lean_ctor_set(v___x_4373_, 5, v_synthPendingDepth_4367_);
lean_ctor_set(v___x_4373_, 6, v_customCanUnfoldPredicate_x3f_4368_);
lean_ctor_set_uint8(v___x_4373_, sizeof(void*)*7, v___x_4372_);
lean_ctor_set_uint8(v___x_4373_, sizeof(void*)*7 + 1, v_univApprox_4369_);
lean_ctor_set_uint8(v___x_4373_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4370_);
lean_ctor_set_uint8(v___x_4373_, sizeof(void*)*7 + 3, v_cacheInferType_4371_);
v___x_4374_ = lean_st_ref_take(v___y_4331_);
v_mctx_4375_ = lean_ctor_get(v___x_4374_, 0);
v_cache_4376_ = lean_ctor_get(v___x_4374_, 1);
v_zetaDeltaFVarIds_4377_ = lean_ctor_get(v___x_4374_, 2);
v_postponed_4378_ = lean_ctor_get(v___x_4374_, 3);
v_diag_4379_ = lean_ctor_get(v___x_4374_, 4);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4381_ = v___x_4374_;
v_isShared_4382_ = v_isSharedCheck_4424_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_diag_4379_);
lean_inc(v_postponed_4378_);
lean_inc(v_zetaDeltaFVarIds_4377_);
lean_inc(v_cache_4376_);
lean_inc(v_mctx_4375_);
lean_dec(v___x_4374_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4424_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v_a_4384_; lean_object* v_a_4388_; lean_object* v___x_4401_; 
if (v_isShared_4382_ == 0)
{
lean_ctor_set(v___x_4381_, 2, v___x_4335_);
v___x_4401_ = v___x_4381_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_mctx_4375_);
lean_ctor_set(v_reuseFailAlloc_4423_, 1, v_cache_4376_);
lean_ctor_set(v_reuseFailAlloc_4423_, 2, v___x_4335_);
lean_ctor_set(v_reuseFailAlloc_4423_, 3, v_postponed_4378_);
lean_ctor_set(v_reuseFailAlloc_4423_, 4, v_diag_4379_);
v___x_4401_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4400_;
}
v___jp_4383_:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4385_ = lean_box(0);
v___x_4386_ = l_Lean_Meta_Sym_letToHave___lam__4(v___y_4331_, v_zetaDeltaFVarIds_4377_, v___x_4385_);
lean_dec_ref(v___x_4386_);
v_a_4339_ = v_a_4384_;
goto v___jp_4338_;
}
v___jp_4387_:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4398_; 
lean_inc(v_a_4388_);
v___x_4389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4389_, 0, v_a_4388_);
v___x_4390_ = l_Lean_Meta_Sym_letToHave___lam__4(v___y_4331_, v_zetaDeltaFVarIds_4377_, v___x_4389_);
lean_dec_ref(v___x_4390_);
v___x_4391_ = l_Lean_Meta_Sym_letToHave___lam__3(v___y_4331_, v_cache_4337_, v___x_4389_);
lean_dec_ref_known(v___x_4389_, 1);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4398_ == 0)
{
lean_object* v_unused_4399_; 
v_unused_4399_ = lean_ctor_get(v___x_4391_, 0);
lean_dec(v_unused_4399_);
v___x_4393_ = v___x_4391_;
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
else
{
lean_dec(v___x_4391_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4396_; 
if (v_isShared_4394_ == 0)
{
lean_ctor_set(v___x_4393_, 0, v_a_4388_);
v___x_4396_ = v___x_4393_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_a_4388_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
}
v_reusejp_4400_:
{
lean_object* v___x_4402_; lean_object* v___x_4403_; uint8_t v_transparency_4404_; uint8_t v___x_4405_; 
v___x_4402_ = lean_st_ref_put(v___y_4331_, v___x_4401_);
v___x_4403_ = l_Lean_Meta_Context_config(v___x_4373_);
lean_dec_ref_known(v___x_4373_, 7);
v_transparency_4404_ = lean_ctor_get_uint8(v___x_4403_, 9);
v___x_4405_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4404_, v___x_4325_);
if (v___x_4405_ == 0)
{
lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; uint64_t v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
lean_dec_ref(v___x_4403_);
lean_inc_ref(v_keyedConfig_4362_);
v___x_4406_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4325_, v_keyedConfig_4362_);
lean_inc_n(v_customCanUnfoldPredicate_x3f_4368_, 2);
lean_inc_n(v_synthPendingDepth_4367_, 2);
lean_inc_n(v_defEqCtx_x3f_4366_, 2);
lean_inc_ref_n(v_localInstances_4365_, 2);
lean_inc_ref_n(v_lctx_4364_, 3);
lean_inc_n(v_zetaDeltaSet_4363_, 2);
v___x_4407_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4407_, 0, v___x_4406_);
lean_ctor_set(v___x_4407_, 1, v_zetaDeltaSet_4363_);
lean_ctor_set(v___x_4407_, 2, v_lctx_4364_);
lean_ctor_set(v___x_4407_, 3, v_localInstances_4365_);
lean_ctor_set(v___x_4407_, 4, v_defEqCtx_x3f_4366_);
lean_ctor_set(v___x_4407_, 5, v_synthPendingDepth_4367_);
lean_ctor_set(v___x_4407_, 6, v_customCanUnfoldPredicate_x3f_4368_);
lean_ctor_set_uint8(v___x_4407_, sizeof(void*)*7, v___x_4372_);
lean_ctor_set_uint8(v___x_4407_, sizeof(void*)*7 + 1, v_univApprox_4369_);
lean_ctor_set_uint8(v___x_4407_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4370_);
lean_ctor_set_uint8(v___x_4407_, sizeof(void*)*7 + 3, v_cacheInferType_4371_);
v___x_4408_ = l_Lean_Meta_Context_config(v___x_4407_);
lean_dec_ref_known(v___x_4407_, 7);
v___x_4409_ = lean_apply_1(v___f_4326_, v___x_4408_);
v___x_4410_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4409_);
v___x_4411_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4411_, 0, v___x_4409_);
lean_ctor_set_uint64(v___x_4411_, sizeof(void*)*1, v___x_4410_);
v___x_4412_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4412_, 0, v___x_4411_);
lean_ctor_set(v___x_4412_, 1, v_zetaDeltaSet_4363_);
lean_ctor_set(v___x_4412_, 2, v_lctx_4364_);
lean_ctor_set(v___x_4412_, 3, v_localInstances_4365_);
lean_ctor_set(v___x_4412_, 4, v_defEqCtx_x3f_4366_);
lean_ctor_set(v___x_4412_, 5, v_synthPendingDepth_4367_);
lean_ctor_set(v___x_4412_, 6, v_customCanUnfoldPredicate_x3f_4368_);
lean_ctor_set_uint8(v___x_4412_, sizeof(void*)*7, v___x_4372_);
lean_ctor_set_uint8(v___x_4412_, sizeof(void*)*7 + 1, v_univApprox_4369_);
lean_ctor_set_uint8(v___x_4412_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4370_);
lean_ctor_set_uint8(v___x_4412_, sizeof(void*)*7 + 3, v_cacheInferType_4371_);
lean_inc(v___y_4333_);
lean_inc_ref(v___y_4332_);
lean_inc(v___y_4331_);
lean_inc(v___y_4329_);
lean_inc_ref(v___y_4328_);
v___x_4413_ = lean_apply_8(v___f_4327_, v_lctx_4364_, v___y_4328_, v___y_4329_, v___x_4412_, v___y_4331_, v___y_4332_, v___y_4333_, lean_box(0));
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v_a_4414_; 
v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
lean_inc(v_a_4414_);
lean_dec_ref_known(v___x_4413_, 1);
v_a_4388_ = v_a_4414_;
goto v___jp_4387_;
}
else
{
lean_object* v_a_4415_; 
v_a_4415_ = lean_ctor_get(v___x_4413_, 0);
lean_inc(v_a_4415_);
lean_dec_ref_known(v___x_4413_, 1);
v_a_4384_ = v_a_4415_;
goto v___jp_4383_;
}
}
else
{
lean_object* v___x_4416_; uint64_t v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
v___x_4416_ = lean_apply_1(v___f_4326_, v___x_4403_);
v___x_4417_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4416_);
v___x_4418_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4418_, 0, v___x_4416_);
lean_ctor_set_uint64(v___x_4418_, sizeof(void*)*1, v___x_4417_);
lean_inc(v_customCanUnfoldPredicate_x3f_4368_);
lean_inc(v_synthPendingDepth_4367_);
lean_inc(v_defEqCtx_x3f_4366_);
lean_inc_ref(v_localInstances_4365_);
lean_inc_ref_n(v_lctx_4364_, 2);
lean_inc(v_zetaDeltaSet_4363_);
v___x_4419_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4419_, 0, v___x_4418_);
lean_ctor_set(v___x_4419_, 1, v_zetaDeltaSet_4363_);
lean_ctor_set(v___x_4419_, 2, v_lctx_4364_);
lean_ctor_set(v___x_4419_, 3, v_localInstances_4365_);
lean_ctor_set(v___x_4419_, 4, v_defEqCtx_x3f_4366_);
lean_ctor_set(v___x_4419_, 5, v_synthPendingDepth_4367_);
lean_ctor_set(v___x_4419_, 6, v_customCanUnfoldPredicate_x3f_4368_);
lean_ctor_set_uint8(v___x_4419_, sizeof(void*)*7, v___x_4372_);
lean_ctor_set_uint8(v___x_4419_, sizeof(void*)*7 + 1, v_univApprox_4369_);
lean_ctor_set_uint8(v___x_4419_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4370_);
lean_ctor_set_uint8(v___x_4419_, sizeof(void*)*7 + 3, v_cacheInferType_4371_);
lean_inc(v___y_4333_);
lean_inc_ref(v___y_4332_);
lean_inc(v___y_4331_);
lean_inc(v___y_4329_);
lean_inc_ref(v___y_4328_);
v___x_4420_ = lean_apply_8(v___f_4327_, v_lctx_4364_, v___y_4328_, v___y_4329_, v___x_4419_, v___y_4331_, v___y_4332_, v___y_4333_, lean_box(0));
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v_a_4421_; 
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
lean_inc(v_a_4421_);
lean_dec_ref_known(v___x_4420_, 1);
v_a_4388_ = v_a_4421_;
goto v___jp_4387_;
}
else
{
lean_object* v_a_4422_; 
v_a_4422_ = lean_ctor_get(v___x_4420_, 0);
lean_inc(v_a_4422_);
lean_dec_ref_known(v___x_4420_, 1);
v_a_4384_ = v_a_4422_;
goto v___jp_4383_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__5___boxed(lean_object* v___x_4428_, lean_object* v___f_4429_, lean_object* v___f_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
uint8_t v___x_18556__boxed_4438_; lean_object* v_res_4439_; 
v___x_18556__boxed_4438_ = lean_unbox(v___x_4428_);
v_res_4439_ = l_Lean_Meta_Sym_letToHave___lam__5(v___x_18556__boxed_4438_, v___f_4429_, v___f_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
return v_res_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(lean_object* v_msg_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v_ref_4446_; lean_object* v___x_4447_; lean_object* v_a_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4456_; 
v_ref_4446_ = lean_ctor_get(v___y_4443_, 2);
v___x_4447_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(v_msg_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
v_a_4448_ = lean_ctor_get(v___x_4447_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4447_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4450_ = v___x_4447_;
v_isShared_4451_ = v_isSharedCheck_4456_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_a_4448_);
lean_dec(v___x_4447_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4456_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
lean_object* v___x_4452_; lean_object* v___x_4454_; 
lean_inc(v_ref_4446_);
v___x_4452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4452_, 0, v_ref_4446_);
lean_ctor_set(v___x_4452_, 1, v_a_4448_);
if (v_isShared_4451_ == 0)
{
lean_ctor_set_tag(v___x_4450_, 1);
lean_ctor_set(v___x_4450_, 0, v___x_4452_);
v___x_4454_ = v___x_4450_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v___x_4452_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg___boxed(lean_object* v_msg_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(v_msg_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
lean_dec(v___y_4461_);
lean_dec_ref(v___y_4460_);
lean_dec(v___y_4459_);
lean_dec_ref(v___y_4458_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(lean_object* v___y_4464_, uint8_t v_isExporting_4465_, lean_object* v___x_4466_, lean_object* v___y_4467_, lean_object* v___x_4468_, lean_object* v_a_x3f_4469_){
_start:
{
lean_object* v___x_4471_; lean_object* v_env_4472_; lean_object* v_nextMacroScope_4473_; lean_object* v_ngen_4474_; lean_object* v_auxDeclNGen_4475_; lean_object* v_traceState_4476_; lean_object* v_recordedDeps_4477_; lean_object* v_messages_4478_; lean_object* v_infoState_4479_; lean_object* v_snapshotTasks_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4505_; 
v___x_4471_ = lean_st_ref_take(v___y_4464_);
v_env_4472_ = lean_ctor_get(v___x_4471_, 0);
v_nextMacroScope_4473_ = lean_ctor_get(v___x_4471_, 1);
v_ngen_4474_ = lean_ctor_get(v___x_4471_, 2);
v_auxDeclNGen_4475_ = lean_ctor_get(v___x_4471_, 3);
v_traceState_4476_ = lean_ctor_get(v___x_4471_, 4);
v_recordedDeps_4477_ = lean_ctor_get(v___x_4471_, 6);
v_messages_4478_ = lean_ctor_get(v___x_4471_, 7);
v_infoState_4479_ = lean_ctor_get(v___x_4471_, 8);
v_snapshotTasks_4480_ = lean_ctor_get(v___x_4471_, 9);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4505_ == 0)
{
lean_object* v_unused_4506_; 
v_unused_4506_ = lean_ctor_get(v___x_4471_, 5);
lean_dec(v_unused_4506_);
v___x_4482_ = v___x_4471_;
v_isShared_4483_ = v_isSharedCheck_4505_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_snapshotTasks_4480_);
lean_inc(v_infoState_4479_);
lean_inc(v_messages_4478_);
lean_inc(v_recordedDeps_4477_);
lean_inc(v_traceState_4476_);
lean_inc(v_auxDeclNGen_4475_);
lean_inc(v_ngen_4474_);
lean_inc(v_nextMacroScope_4473_);
lean_inc(v_env_4472_);
lean_dec(v___x_4471_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4505_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4484_; lean_object* v___x_4486_; 
v___x_4484_ = l_Lean_Environment_setExporting(v_env_4472_, v_isExporting_4465_);
if (v_isShared_4483_ == 0)
{
lean_ctor_set(v___x_4482_, 5, v___x_4466_);
lean_ctor_set(v___x_4482_, 0, v___x_4484_);
v___x_4486_ = v___x_4482_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v___x_4484_);
lean_ctor_set(v_reuseFailAlloc_4504_, 1, v_nextMacroScope_4473_);
lean_ctor_set(v_reuseFailAlloc_4504_, 2, v_ngen_4474_);
lean_ctor_set(v_reuseFailAlloc_4504_, 3, v_auxDeclNGen_4475_);
lean_ctor_set(v_reuseFailAlloc_4504_, 4, v_traceState_4476_);
lean_ctor_set(v_reuseFailAlloc_4504_, 5, v___x_4466_);
lean_ctor_set(v_reuseFailAlloc_4504_, 6, v_recordedDeps_4477_);
lean_ctor_set(v_reuseFailAlloc_4504_, 7, v_messages_4478_);
lean_ctor_set(v_reuseFailAlloc_4504_, 8, v_infoState_4479_);
lean_ctor_set(v_reuseFailAlloc_4504_, 9, v_snapshotTasks_4480_);
v___x_4486_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v_mctx_4489_; lean_object* v_zetaDeltaFVarIds_4490_; lean_object* v_postponed_4491_; lean_object* v_diag_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4502_; 
v___x_4487_ = lean_st_ref_put(v___y_4464_, v___x_4486_);
v___x_4488_ = lean_st_ref_take(v___y_4467_);
v_mctx_4489_ = lean_ctor_get(v___x_4488_, 0);
v_zetaDeltaFVarIds_4490_ = lean_ctor_get(v___x_4488_, 2);
v_postponed_4491_ = lean_ctor_get(v___x_4488_, 3);
v_diag_4492_ = lean_ctor_get(v___x_4488_, 4);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4502_ == 0)
{
lean_object* v_unused_4503_; 
v_unused_4503_ = lean_ctor_get(v___x_4488_, 1);
lean_dec(v_unused_4503_);
v___x_4494_ = v___x_4488_;
v_isShared_4495_ = v_isSharedCheck_4502_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_diag_4492_);
lean_inc(v_postponed_4491_);
lean_inc(v_zetaDeltaFVarIds_4490_);
lean_inc(v_mctx_4489_);
lean_dec(v___x_4488_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4502_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4496_; lean_object* v___x_4498_; 
v___x_4496_ = lean_box(0);
if (v_isShared_4495_ == 0)
{
lean_ctor_set(v___x_4494_, 1, v___x_4468_);
v___x_4498_ = v___x_4494_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_mctx_4489_);
lean_ctor_set(v_reuseFailAlloc_4501_, 1, v___x_4468_);
lean_ctor_set(v_reuseFailAlloc_4501_, 2, v_zetaDeltaFVarIds_4490_);
lean_ctor_set(v_reuseFailAlloc_4501_, 3, v_postponed_4491_);
lean_ctor_set(v_reuseFailAlloc_4501_, 4, v_diag_4492_);
v___x_4498_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
lean_object* v___x_4499_; lean_object* v___x_4500_; 
v___x_4499_ = lean_st_ref_put(v___y_4467_, v___x_4498_);
v___x_4500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4496_);
return v___x_4500_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_4507_, lean_object* v_isExporting_4508_, lean_object* v___x_4509_, lean_object* v___y_4510_, lean_object* v___x_4511_, lean_object* v_a_x3f_4512_, lean_object* v___y_4513_){
_start:
{
uint8_t v_isExporting_boxed_4514_; lean_object* v_res_4515_; 
v_isExporting_boxed_4514_ = lean_unbox(v_isExporting_4508_);
v_res_4515_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(v___y_4507_, v_isExporting_boxed_4514_, v___x_4509_, v___y_4510_, v___x_4511_, v_a_x3f_4512_);
lean_dec(v_a_x3f_4512_);
lean_dec(v___y_4510_);
lean_dec(v___y_4507_);
return v_res_4515_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4516_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__5___closed__0, &l_Lean_Meta_Sym_letToHave___lam__5___closed__0_once, _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__0);
v___x_4517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4516_);
return v___x_4517_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___x_4518_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0);
v___x_4519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4518_);
lean_ctor_set(v___x_4519_, 1, v___x_4518_);
return v___x_4519_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4520_; lean_object* v___x_4521_; 
v___x_4520_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0);
v___x_4521_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4521_, 0, v___x_4520_);
lean_ctor_set(v___x_4521_, 1, v___x_4520_);
lean_ctor_set(v___x_4521_, 2, v___x_4520_);
lean_ctor_set(v___x_4521_, 3, v___x_4520_);
lean_ctor_set(v___x_4521_, 4, v___x_4520_);
lean_ctor_set(v___x_4521_, 5, v___x_4520_);
return v___x_4521_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(lean_object* v_x_4522_, uint8_t v_isExporting_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
lean_object* v___x_4531_; lean_object* v_env_4532_; lean_object* v___x_4533_; uint8_t v_isModule_4534_; 
v___x_4531_ = lean_st_ref_get(v___y_4529_);
v_env_4532_ = lean_ctor_get(v___x_4531_, 0);
lean_inc_ref(v_env_4532_);
lean_dec(v___x_4531_);
v___x_4533_ = l_Lean_Environment_header(v_env_4532_);
v_isModule_4534_ = lean_ctor_get_uint8(v___x_4533_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4533_);
if (v_isModule_4534_ == 0)
{
lean_object* v___x_4535_; 
lean_dec_ref(v_env_4532_);
lean_inc(v___y_4529_);
lean_inc_ref(v___y_4528_);
lean_inc(v___y_4527_);
lean_inc_ref(v___y_4526_);
lean_inc(v___y_4525_);
lean_inc_ref(v___y_4524_);
v___x_4535_ = lean_apply_7(v_x_4522_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, lean_box(0));
return v___x_4535_;
}
else
{
uint8_t v_isExporting_4536_; 
v_isExporting_4536_ = lean_ctor_get_uint8(v_env_4532_, sizeof(void*)*8);
lean_dec_ref(v_env_4532_);
if (v_isExporting_4523_ == 0)
{
if (v_isExporting_4536_ == 0)
{
lean_object* v___x_4603_; 
lean_inc(v___y_4529_);
lean_inc_ref(v___y_4528_);
lean_inc(v___y_4527_);
lean_inc_ref(v___y_4526_);
lean_inc(v___y_4525_);
lean_inc_ref(v___y_4524_);
v___x_4603_ = lean_apply_7(v_x_4522_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, lean_box(0));
return v___x_4603_;
}
else
{
goto v___jp_4537_;
}
}
else
{
if (v_isExporting_4536_ == 0)
{
goto v___jp_4537_;
}
else
{
lean_object* v___x_4604_; 
lean_inc(v___y_4529_);
lean_inc_ref(v___y_4528_);
lean_inc(v___y_4527_);
lean_inc_ref(v___y_4526_);
lean_inc(v___y_4525_);
lean_inc_ref(v___y_4524_);
v___x_4604_ = lean_apply_7(v_x_4522_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, lean_box(0));
return v___x_4604_;
}
}
v___jp_4537_:
{
lean_object* v___x_4538_; lean_object* v_env_4539_; lean_object* v_nextMacroScope_4540_; lean_object* v_ngen_4541_; lean_object* v_auxDeclNGen_4542_; lean_object* v_traceState_4543_; lean_object* v_recordedDeps_4544_; lean_object* v_messages_4545_; lean_object* v_infoState_4546_; lean_object* v_snapshotTasks_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4601_; 
v___x_4538_ = lean_st_ref_take(v___y_4529_);
v_env_4539_ = lean_ctor_get(v___x_4538_, 0);
v_nextMacroScope_4540_ = lean_ctor_get(v___x_4538_, 1);
v_ngen_4541_ = lean_ctor_get(v___x_4538_, 2);
v_auxDeclNGen_4542_ = lean_ctor_get(v___x_4538_, 3);
v_traceState_4543_ = lean_ctor_get(v___x_4538_, 4);
v_recordedDeps_4544_ = lean_ctor_get(v___x_4538_, 6);
v_messages_4545_ = lean_ctor_get(v___x_4538_, 7);
v_infoState_4546_ = lean_ctor_get(v___x_4538_, 8);
v_snapshotTasks_4547_ = lean_ctor_get(v___x_4538_, 9);
v_isSharedCheck_4601_ = !lean_is_exclusive(v___x_4538_);
if (v_isSharedCheck_4601_ == 0)
{
lean_object* v_unused_4602_; 
v_unused_4602_ = lean_ctor_get(v___x_4538_, 5);
lean_dec(v_unused_4602_);
v___x_4549_ = v___x_4538_;
v_isShared_4550_ = v_isSharedCheck_4601_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_snapshotTasks_4547_);
lean_inc(v_infoState_4546_);
lean_inc(v_messages_4545_);
lean_inc(v_recordedDeps_4544_);
lean_inc(v_traceState_4543_);
lean_inc(v_auxDeclNGen_4542_);
lean_inc(v_ngen_4541_);
lean_inc(v_nextMacroScope_4540_);
lean_inc(v_env_4539_);
lean_dec(v___x_4538_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4601_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4554_; 
v___x_4551_ = l_Lean_Environment_setExporting(v_env_4539_, v_isExporting_4523_);
v___x_4552_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1);
if (v_isShared_4550_ == 0)
{
lean_ctor_set(v___x_4549_, 5, v___x_4552_);
lean_ctor_set(v___x_4549_, 0, v___x_4551_);
v___x_4554_ = v___x_4549_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v___x_4551_);
lean_ctor_set(v_reuseFailAlloc_4600_, 1, v_nextMacroScope_4540_);
lean_ctor_set(v_reuseFailAlloc_4600_, 2, v_ngen_4541_);
lean_ctor_set(v_reuseFailAlloc_4600_, 3, v_auxDeclNGen_4542_);
lean_ctor_set(v_reuseFailAlloc_4600_, 4, v_traceState_4543_);
lean_ctor_set(v_reuseFailAlloc_4600_, 5, v___x_4552_);
lean_ctor_set(v_reuseFailAlloc_4600_, 6, v_recordedDeps_4544_);
lean_ctor_set(v_reuseFailAlloc_4600_, 7, v_messages_4545_);
lean_ctor_set(v_reuseFailAlloc_4600_, 8, v_infoState_4546_);
lean_ctor_set(v_reuseFailAlloc_4600_, 9, v_snapshotTasks_4547_);
v___x_4554_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v_mctx_4557_; lean_object* v_zetaDeltaFVarIds_4558_; lean_object* v_postponed_4559_; lean_object* v_diag_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4598_; 
v___x_4555_ = lean_st_ref_put(v___y_4529_, v___x_4554_);
v___x_4556_ = lean_st_ref_take(v___y_4527_);
v_mctx_4557_ = lean_ctor_get(v___x_4556_, 0);
v_zetaDeltaFVarIds_4558_ = lean_ctor_get(v___x_4556_, 2);
v_postponed_4559_ = lean_ctor_get(v___x_4556_, 3);
v_diag_4560_ = lean_ctor_get(v___x_4556_, 4);
v_isSharedCheck_4598_ = !lean_is_exclusive(v___x_4556_);
if (v_isSharedCheck_4598_ == 0)
{
lean_object* v_unused_4599_; 
v_unused_4599_ = lean_ctor_get(v___x_4556_, 1);
lean_dec(v_unused_4599_);
v___x_4562_ = v___x_4556_;
v_isShared_4563_ = v_isSharedCheck_4598_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_diag_4560_);
lean_inc(v_postponed_4559_);
lean_inc(v_zetaDeltaFVarIds_4558_);
lean_inc(v_mctx_4557_);
lean_dec(v___x_4556_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4598_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
lean_object* v___x_4564_; lean_object* v___x_4566_; 
v___x_4564_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2);
if (v_isShared_4563_ == 0)
{
lean_ctor_set(v___x_4562_, 1, v___x_4564_);
v___x_4566_ = v___x_4562_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_mctx_4557_);
lean_ctor_set(v_reuseFailAlloc_4597_, 1, v___x_4564_);
lean_ctor_set(v_reuseFailAlloc_4597_, 2, v_zetaDeltaFVarIds_4558_);
lean_ctor_set(v_reuseFailAlloc_4597_, 3, v_postponed_4559_);
lean_ctor_set(v_reuseFailAlloc_4597_, 4, v_diag_4560_);
v___x_4566_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
lean_object* v___x_4567_; lean_object* v_r_4568_; 
v___x_4567_ = lean_st_ref_put(v___y_4527_, v___x_4566_);
lean_inc(v___y_4529_);
lean_inc_ref(v___y_4528_);
lean_inc(v___y_4527_);
lean_inc_ref(v___y_4526_);
lean_inc(v___y_4525_);
lean_inc_ref(v___y_4524_);
v_r_4568_ = lean_apply_7(v_x_4522_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, lean_box(0));
if (lean_obj_tag(v_r_4568_) == 0)
{
lean_object* v_a_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4585_; 
v_a_4569_ = lean_ctor_get(v_r_4568_, 0);
v_isSharedCheck_4585_ = !lean_is_exclusive(v_r_4568_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4571_ = v_r_4568_;
v_isShared_4572_ = v_isSharedCheck_4585_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_a_4569_);
lean_dec(v_r_4568_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4585_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v___x_4574_; 
lean_inc(v_a_4569_);
if (v_isShared_4572_ == 0)
{
lean_ctor_set_tag(v___x_4571_, 1);
v___x_4574_ = v___x_4571_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v_a_4569_);
v___x_4574_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
lean_object* v___x_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4582_; 
v___x_4575_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(v___y_4529_, v_isExporting_4536_, v___x_4552_, v___y_4527_, v___x_4564_, v___x_4574_);
lean_dec_ref(v___x_4574_);
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
lean_ctor_set(v___x_4577_, 0, v_a_4569_);
v___x_4580_ = v___x_4577_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_a_4569_);
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
else
{
lean_object* v_a_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4595_; 
v_a_4586_ = lean_ctor_get(v_r_4568_, 0);
lean_inc(v_a_4586_);
lean_dec_ref_known(v_r_4568_, 1);
v___x_4587_ = lean_box(0);
v___x_4588_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(v___y_4529_, v_isExporting_4536_, v___x_4552_, v___y_4527_, v___x_4564_, v___x_4587_);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4588_);
if (v_isSharedCheck_4595_ == 0)
{
lean_object* v_unused_4596_; 
v_unused_4596_ = lean_ctor_get(v___x_4588_, 0);
lean_dec(v_unused_4596_);
v___x_4590_ = v___x_4588_;
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
else
{
lean_dec(v___x_4588_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___x_4593_; 
if (v_isShared_4591_ == 0)
{
lean_ctor_set_tag(v___x_4590_, 1);
lean_ctor_set(v___x_4590_, 0, v_a_4586_);
v___x_4593_ = v___x_4590_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_a_4586_);
v___x_4593_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
return v___x_4593_;
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
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___boxed(lean_object* v_x_4605_, lean_object* v_isExporting_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_){
_start:
{
uint8_t v_isExporting_boxed_4614_; lean_object* v_res_4615_; 
v_isExporting_boxed_4614_ = lean_unbox(v_isExporting_4606_);
v_res_4615_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(v_x_4605_, v_isExporting_boxed_4614_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_);
lean_dec(v___y_4612_);
lean_dec_ref(v___y_4611_);
lean_dec(v___y_4610_);
lean_dec_ref(v___y_4609_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(lean_object* v_x_4616_, uint8_t v_when_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_){
_start:
{
if (v_when_4617_ == 0)
{
lean_object* v___x_4625_; 
lean_inc(v___y_4623_);
lean_inc_ref(v___y_4622_);
lean_inc(v___y_4621_);
lean_inc_ref(v___y_4620_);
lean_inc(v___y_4619_);
lean_inc_ref(v___y_4618_);
v___x_4625_ = lean_apply_7(v_x_4616_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, lean_box(0));
return v___x_4625_;
}
else
{
uint8_t v___x_4626_; lean_object* v___x_4627_; 
v___x_4626_ = 0;
v___x_4627_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(v_x_4616_, v___x_4626_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_);
return v___x_4627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg___boxed(lean_object* v_x_4628_, lean_object* v_when_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_){
_start:
{
uint8_t v_when_boxed_4637_; lean_object* v_res_4638_; 
v_when_boxed_4637_ = lean_unbox(v_when_4629_);
v_res_4638_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(v_x_4628_, v_when_boxed_4637_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
lean_dec(v___y_4635_);
lean_dec_ref(v___y_4634_);
lean_dec(v___y_4633_);
lean_dec_ref(v___y_4632_);
lean_dec(v___y_4631_);
lean_dec_ref(v___y_4630_);
return v_res_4638_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___closed__2(void){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4641_ = ((lean_object*)(l_Lean_Meta_Sym_letToHave___closed__1));
v___x_4642_ = l_Lean_stringToMessageData(v___x_4641_);
return v___x_4642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave(lean_object* v_e_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_){
_start:
{
lean_object* v___f_4651_; lean_object* v___f_4652_; lean_object* v___y_4654_; lean_object* v___y_4655_; lean_object* v___y_4656_; lean_object* v___y_4657_; lean_object* v___y_4658_; lean_object* v___y_4659_; uint8_t v___x_4668_; 
v___f_4651_ = ((lean_object*)(l_Lean_Meta_Sym_letToHave___closed__0));
lean_inc_ref(v_e_4643_);
v___f_4652_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_letToHave___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4652_, 0, v_e_4643_);
v___x_4668_ = l_Lean_Expr_hasLooseBVars(v_e_4643_);
lean_dec_ref(v_e_4643_);
if (v___x_4668_ == 0)
{
v___y_4654_ = v_a_4644_;
v___y_4655_ = v_a_4645_;
v___y_4656_ = v_a_4646_;
v___y_4657_ = v_a_4647_;
v___y_4658_ = v_a_4648_;
v___y_4659_ = v_a_4649_;
goto v___jp_4653_;
}
else
{
lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4678_; 
lean_dec_ref(v___f_4652_);
v___x_4669_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___closed__2, &l_Lean_Meta_Sym_letToHave___closed__2_once, _init_l_Lean_Meta_Sym_letToHave___closed__2);
v___x_4670_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(v___x_4669_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_);
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4673_ = v___x_4670_;
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4670_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4676_; 
if (v_isShared_4674_ == 0)
{
v___x_4676_ = v___x_4673_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_a_4671_);
v___x_4676_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
return v___x_4676_;
}
}
}
v___jp_4653_:
{
uint8_t v___x_4660_; lean_object* v___x_4661_; lean_object* v___f_4662_; uint8_t v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; uint8_t v___x_4666_; lean_object* v___x_4667_; 
v___x_4660_ = 0;
v___x_4661_ = lean_box(v___x_4660_);
v___f_4662_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_letToHave___lam__5___boxed), 10, 3);
lean_closure_set(v___f_4662_, 0, v___x_4661_);
lean_closure_set(v___f_4662_, 1, v___f_4651_);
lean_closure_set(v___f_4662_, 2, v___f_4652_);
v___x_4663_ = 0;
v___x_4664_ = lean_box(v___x_4663_);
v___x_4665_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___boxed), 10, 3);
lean_closure_set(v___x_4665_, 0, lean_box(0));
lean_closure_set(v___x_4665_, 1, v___f_4662_);
lean_closure_set(v___x_4665_, 2, v___x_4664_);
v___x_4666_ = 1;
v___x_4667_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(v___x_4665_, v___x_4666_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
return v___x_4667_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___boxed(lean_object* v_e_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_){
_start:
{
lean_object* v_res_4687_; 
v_res_4687_ = l_Lean_Meta_Sym_letToHave(v_e_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_);
lean_dec(v_a_4685_);
lean_dec_ref(v_a_4684_);
lean_dec(v_a_4683_);
lean_dec_ref(v_a_4682_);
lean_dec(v_a_4681_);
lean_dec_ref(v_a_4680_);
return v_res_4687_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2(lean_object* v_00_u03b1_4688_, lean_object* v_x_4689_, uint8_t v_isExporting_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_){
_start:
{
lean_object* v___x_4698_; 
v___x_4698_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(v_x_4689_, v_isExporting_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___boxed(lean_object* v_00_u03b1_4699_, lean_object* v_x_4700_, lean_object* v_isExporting_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
uint8_t v_isExporting_boxed_4709_; lean_object* v_res_4710_; 
v_isExporting_boxed_4709_ = lean_unbox(v_isExporting_4701_);
v_res_4710_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2(v_00_u03b1_4699_, v_x_4700_, v_isExporting_boxed_4709_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_);
lean_dec(v___y_4707_);
lean_dec_ref(v___y_4706_);
lean_dec(v___y_4705_);
lean_dec_ref(v___y_4704_);
lean_dec(v___y_4703_);
lean_dec_ref(v___y_4702_);
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2(lean_object* v_00_u03b1_4711_, lean_object* v_x_4712_, uint8_t v_when_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_){
_start:
{
lean_object* v___x_4721_; 
v___x_4721_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(v_x_4712_, v_when_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_);
return v___x_4721_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___boxed(lean_object* v_00_u03b1_4722_, lean_object* v_x_4723_, lean_object* v_when_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_){
_start:
{
uint8_t v_when_boxed_4732_; lean_object* v_res_4733_; 
v_when_boxed_4732_ = lean_unbox(v_when_4724_);
v_res_4733_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2(v_00_u03b1_4722_, v_x_4723_, v_when_boxed_4732_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_);
lean_dec(v___y_4730_);
lean_dec_ref(v___y_4729_);
lean_dec(v___y_4728_);
lean_dec_ref(v___y_4727_);
lean_dec(v___y_4726_);
lean_dec_ref(v___y_4725_);
return v_res_4733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3(lean_object* v_00_u03b1_4734_, lean_object* v_msg_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_){
_start:
{
lean_object* v___x_4743_; 
v___x_4743_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(v_msg_4735_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___boxed(lean_object* v_00_u03b1_4744_, lean_object* v_msg_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_){
_start:
{
lean_object* v_res_4753_; 
v_res_4753_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3(v_00_u03b1_4744_, v_msg_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
lean_dec(v___y_4751_);
lean_dec_ref(v___y_4750_);
lean_dec(v___y_4749_);
lean_dec_ref(v___y_4748_);
lean_dec(v___y_4747_);
lean_dec_ref(v___y_4746_);
return v_res_4753_;
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
