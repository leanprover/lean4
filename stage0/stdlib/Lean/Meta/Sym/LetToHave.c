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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___lam__0(lean_object* v_a_1_, lean_object* v_visited_2_, lean_object* v_types_3_, lean_object* v_subst_4_, lean_object* v_a_x3f_5_){
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
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_visited_2_ = stack[1].m_obj;
lean_object* v_types_3_ = stack[2].m_obj;
lean_object* v_subst_4_ = stack[3].m_obj;
lean_object* v_a_x3f_5_ = stack[4].m_obj;
lean_object* v_res_24_;
v_res_24_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___lam__0(v_a_1_, v_visited_2_, v_types_3_, v_subst_4_, v_a_x3f_5_);
stack->m_obj
 = v_res_24_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___lam__0___boxed(lean_object* v_a_25_, lean_object* v_visited_26_, lean_object* v_types_27_, lean_object* v_subst_28_, lean_object* v_a_x3f_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___lam__0(v_a_25_, v_visited_26_, v_types_27_, v_subst_28_, v_a_x3f_29_);
lean_dec(v_a_x3f_29_);
lean_dec(v_a_25_);
return v_res_31_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__0(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_32_ = lean_box(0);
v___x_33_ = lean_unsigned_to_nat(16u);
v___x_34_ = lean_mk_array(v___x_33_, v___x_32_);
return v___x_34_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_35_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__0, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__0);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
lean_ctor_set(v___x_37_, 1, v___x_35_);
return v___x_37_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg(lean_object* v_x_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v___x_48_; lean_object* v_visited_49_; lean_object* v_types_50_; lean_object* v_subst_51_; lean_object* v_visitedClosed_52_; lean_object* v_hasDepLetCache_53_; lean_object* v_numConverted_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_92_; 
v___x_48_ = lean_st_ref_take(v_a_40_);
v_visited_49_ = lean_ctor_get(v___x_48_, 0);
v_types_50_ = lean_ctor_get(v___x_48_, 1);
v_subst_51_ = lean_ctor_get(v___x_48_, 2);
v_visitedClosed_52_ = lean_ctor_get(v___x_48_, 3);
v_hasDepLetCache_53_ = lean_ctor_get(v___x_48_, 4);
v_numConverted_54_ = lean_ctor_get(v___x_48_, 5);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_48_);
if (v_isSharedCheck_92_ == 0)
{
v___x_56_ = v___x_48_;
v_isShared_57_ = v_isSharedCheck_92_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_numConverted_54_);
lean_inc(v_hasDepLetCache_53_);
lean_inc(v_visitedClosed_52_);
lean_inc(v_subst_51_);
lean_inc(v_types_50_);
lean_inc(v_visited_49_);
lean_dec(v___x_48_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_92_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_58_; lean_object* v___x_60_; 
v___x_58_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 2, v___x_58_);
lean_ctor_set(v___x_56_, 1, v___x_58_);
lean_ctor_set(v___x_56_, 0, v___x_58_);
v___x_60_ = v___x_56_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_91_, 2, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_91_, 3, v_visitedClosed_52_);
lean_ctor_set(v_reuseFailAlloc_91_, 4, v_hasDepLetCache_53_);
lean_ctor_set(v_reuseFailAlloc_91_, 5, v_numConverted_54_);
v___x_60_ = v_reuseFailAlloc_91_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
lean_object* v___x_61_; lean_object* v_r_62_; 
v___x_61_ = lean_st_ref_put(v_a_40_, v___x_60_);
lean_inc(v_a_46_);
lean_inc_ref(v_a_45_);
lean_inc(v_a_44_);
lean_inc_ref(v_a_43_);
lean_inc(v_a_42_);
lean_inc_ref(v_a_41_);
lean_inc(v_a_40_);
lean_inc_ref(v_a_39_);
v_r_62_ = lean_apply_9(v_x_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, lean_box(0));
if (lean_obj_tag(v_r_62_) == 0)
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_79_; 
v_a_63_ = lean_ctor_get(v_r_62_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v_r_62_);
if (v_isSharedCheck_79_ == 0)
{
v___x_65_ = v_r_62_;
v_isShared_66_ = v_isSharedCheck_79_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v_r_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_79_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
lean_inc(v_a_63_);
if (v_isShared_66_ == 0)
{
lean_ctor_set_tag(v___x_65_, 1);
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_a_63_);
v___x_68_ = v_reuseFailAlloc_78_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
lean_object* v___x_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_76_; 
v___x_69_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___lam__0(v_a_40_, v_visited_49_, v_types_50_, v_subst_51_, v___x_68_);
lean_dec_ref(v___x_68_);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_76_ == 0)
{
lean_object* v_unused_77_; 
v_unused_77_ = lean_ctor_get(v___x_69_, 0);
lean_dec(v_unused_77_);
v___x_71_ = v___x_69_;
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
else
{
lean_dec(v___x_69_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_74_; 
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v_a_63_);
v___x_74_ = v___x_71_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_a_63_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
}
else
{
lean_object* v_a_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_89_; 
v_a_80_ = lean_ctor_get(v_r_62_, 0);
lean_inc(v_a_80_);
lean_dec_ref_known(v_r_62_, 1);
v___x_81_ = lean_box(0);
v___x_82_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___lam__0(v_a_40_, v_visited_49_, v_types_50_, v_subst_51_, v___x_81_);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; 
v_unused_90_ = lean_ctor_get(v___x_82_, 0);
lean_dec(v_unused_90_);
v___x_84_ = v___x_82_;
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
else
{
lean_dec(v___x_82_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_87_; 
if (v_isShared_85_ == 0)
{
lean_ctor_set_tag(v___x_84_, 1);
lean_ctor_set(v___x_84_, 0, v_a_80_);
v___x_87_ = v___x_84_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_a_80_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_38_ = stack[0].m_obj;
lean_object* v_a_39_ = stack[1].m_obj;
lean_object* v_a_40_ = stack[2].m_obj;
lean_object* v_a_41_ = stack[3].m_obj;
lean_object* v_a_42_ = stack[4].m_obj;
lean_object* v_a_43_ = stack[5].m_obj;
lean_object* v_a_44_ = stack[6].m_obj;
lean_object* v_a_45_ = stack[7].m_obj;
lean_object* v_a_46_ = stack[8].m_obj;
lean_object* v_res_93_;
v_res_93_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg(v_x_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_);
stack->m_obj
 = v_res_93_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___boxed(lean_object* v_x_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg(v_x_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
return v_res_104_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope(lean_object* v_00_u03b1_105_, lean_object* v_x_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v___x_116_; lean_object* v_visited_117_; lean_object* v_types_118_; lean_object* v_subst_119_; lean_object* v_visitedClosed_120_; lean_object* v_hasDepLetCache_121_; lean_object* v_numConverted_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_160_; 
v___x_116_ = lean_st_ref_take(v_a_108_);
v_visited_117_ = lean_ctor_get(v___x_116_, 0);
v_types_118_ = lean_ctor_get(v___x_116_, 1);
v_subst_119_ = lean_ctor_get(v___x_116_, 2);
v_visitedClosed_120_ = lean_ctor_get(v___x_116_, 3);
v_hasDepLetCache_121_ = lean_ctor_get(v___x_116_, 4);
v_numConverted_122_ = lean_ctor_get(v___x_116_, 5);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_160_ == 0)
{
v___x_124_ = v___x_116_;
v_isShared_125_ = v_isSharedCheck_160_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_numConverted_122_);
lean_inc(v_hasDepLetCache_121_);
lean_inc(v_visitedClosed_120_);
lean_inc(v_subst_119_);
lean_inc(v_types_118_);
lean_inc(v_visited_117_);
lean_dec(v___x_116_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_160_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 2, v___x_126_);
lean_ctor_set(v___x_124_, 1, v___x_126_);
lean_ctor_set(v___x_124_, 0, v___x_126_);
v___x_128_ = v___x_124_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_159_, 2, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_159_, 3, v_visitedClosed_120_);
lean_ctor_set(v_reuseFailAlloc_159_, 4, v_hasDepLetCache_121_);
lean_ctor_set(v_reuseFailAlloc_159_, 5, v_numConverted_122_);
v___x_128_ = v_reuseFailAlloc_159_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___x_129_; lean_object* v_r_130_; 
v___x_129_ = lean_st_ref_put(v_a_108_, v___x_128_);
lean_inc(v_a_114_);
lean_inc_ref(v_a_113_);
lean_inc(v_a_112_);
lean_inc_ref(v_a_111_);
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
v_r_130_ = lean_apply_9(v_x_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, lean_box(0));
if (lean_obj_tag(v_r_130_) == 0)
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_147_; 
v_a_131_ = lean_ctor_get(v_r_130_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v_r_130_);
if (v_isSharedCheck_147_ == 0)
{
v___x_133_ = v_r_130_;
v_isShared_134_ = v_isSharedCheck_147_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v_r_130_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_147_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
lean_inc(v_a_131_);
if (v_isShared_134_ == 0)
{
lean_ctor_set_tag(v___x_133_, 1);
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_131_);
v___x_136_ = v_reuseFailAlloc_146_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
v___x_137_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___lam__0(v_a_108_, v_visited_117_, v_types_118_, v_subst_119_, v___x_136_);
lean_dec_ref(v___x_136_);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_144_ == 0)
{
lean_object* v_unused_145_; 
v_unused_145_ = lean_ctor_get(v___x_137_, 0);
lean_dec(v_unused_145_);
v___x_139_ = v___x_137_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_dec(v___x_137_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 0, v_a_131_);
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_131_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
else
{
lean_object* v_a_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
v_a_148_ = lean_ctor_get(v_r_130_, 0);
lean_inc(v_a_148_);
lean_dec_ref_known(v_r_130_, 1);
v___x_149_ = lean_box(0);
v___x_150_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___lam__0(v_a_108_, v_visited_117_, v_types_118_, v_subst_119_, v___x_149_);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; 
v_unused_158_ = lean_ctor_get(v___x_150_, 0);
lean_dec(v_unused_158_);
v___x_152_ = v___x_150_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_dec(v___x_150_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
lean_ctor_set_tag(v___x_152_, 1);
lean_ctor_set(v___x_152_, 0, v_a_148_);
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_148_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_106_ = stack[1].m_obj;
lean_object* v_a_107_ = stack[2].m_obj;
lean_object* v_a_108_ = stack[3].m_obj;
lean_object* v_a_109_ = stack[4].m_obj;
lean_object* v_a_110_ = stack[5].m_obj;
lean_object* v_a_111_ = stack[6].m_obj;
lean_object* v_a_112_ = stack[7].m_obj;
lean_object* v_a_113_ = stack[8].m_obj;
lean_object* v_a_114_ = stack[9].m_obj;
lean_object* v_res_161_;
v_res_161_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope(lean_box(0), v_x_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
stack->m_obj
 = v_res_161_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___boxed(lean_object* v_00_u03b1_162_, lean_object* v_x_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope(v_00_u03b1_162_, v_x_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
if (lean_obj_tag(v_x_175_) == 0)
{
return v_x_174_;
}
else
{
lean_object* v_key_176_; lean_object* v_value_177_; lean_object* v_tail_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_204_; 
v_key_176_ = lean_ctor_get(v_x_175_, 0);
v_value_177_ = lean_ctor_get(v_x_175_, 1);
v_tail_178_ = lean_ctor_get(v_x_175_, 2);
v_isSharedCheck_204_ = !lean_is_exclusive(v_x_175_);
if (v_isSharedCheck_204_ == 0)
{
v___x_180_ = v_x_175_;
v_isShared_181_ = v_isSharedCheck_204_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_tail_178_);
lean_inc(v_value_177_);
lean_inc(v_key_176_);
lean_dec(v_x_175_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_204_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; size_t v___x_183_; size_t v___x_184_; size_t v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; uint64_t v___x_188_; uint64_t v_fold_189_; uint64_t v___x_190_; uint64_t v___x_191_; uint64_t v___x_192_; size_t v___x_193_; size_t v___x_194_; size_t v___x_195_; size_t v___x_196_; size_t v___x_197_; lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_182_ = lean_array_get_size(v_x_174_);
v___x_183_ = lean_ptr_addr(v_key_176_);
v___x_184_ = ((size_t)3ULL);
v___x_185_ = lean_usize_shift_right(v___x_183_, v___x_184_);
v___x_186_ = lean_usize_to_uint64(v___x_185_);
v___x_187_ = 32ULL;
v___x_188_ = lean_uint64_shift_right(v___x_186_, v___x_187_);
v_fold_189_ = lean_uint64_xor(v___x_186_, v___x_188_);
v___x_190_ = 16ULL;
v___x_191_ = lean_uint64_shift_right(v_fold_189_, v___x_190_);
v___x_192_ = lean_uint64_xor(v_fold_189_, v___x_191_);
v___x_193_ = lean_uint64_to_usize(v___x_192_);
v___x_194_ = lean_usize_of_nat(v___x_182_);
v___x_195_ = ((size_t)1ULL);
v___x_196_ = lean_usize_sub(v___x_194_, v___x_195_);
v___x_197_ = lean_usize_land(v___x_193_, v___x_196_);
v___x_198_ = lean_array_uget_borrowed(v_x_174_, v___x_197_);
lean_inc(v___x_198_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 2, v___x_198_);
v___x_200_ = v___x_180_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_key_176_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_value_177_);
lean_ctor_set(v_reuseFailAlloc_203_, 2, v___x_198_);
v___x_200_ = v_reuseFailAlloc_203_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_201_; 
v___x_201_ = lean_array_uset(v_x_174_, v___x_197_, v___x_200_);
v_x_174_ = v___x_201_;
v_x_175_ = v_tail_178_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4___redArg(lean_object* v_i_205_, lean_object* v_source_206_, lean_object* v_target_207_){
_start:
{
lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_208_ = lean_array_get_size(v_source_206_);
v___x_209_ = lean_nat_dec_lt(v_i_205_, v___x_208_);
if (v___x_209_ == 0)
{
lean_dec_ref(v_source_206_);
lean_dec(v_i_205_);
return v_target_207_;
}
else
{
lean_object* v_es_210_; lean_object* v___x_211_; lean_object* v_source_212_; lean_object* v_target_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_es_210_ = lean_array_fget(v_source_206_, v_i_205_);
v___x_211_ = lean_box(0);
v_source_212_ = lean_array_fset(v_source_206_, v_i_205_, v___x_211_);
v_target_213_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4_spec__5___redArg(v_target_207_, v_es_210_);
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = lean_nat_add(v_i_205_, v___x_214_);
lean_dec(v_i_205_);
v_i_205_ = v___x_215_;
v_source_206_ = v_source_212_;
v_target_207_ = v_target_213_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3___redArg(lean_object* v_data_217_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v_nbuckets_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_218_ = lean_array_get_size(v_data_217_);
v___x_219_ = lean_unsigned_to_nat(2u);
v_nbuckets_220_ = lean_nat_mul(v___x_218_, v___x_219_);
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_box(0);
v___x_223_ = lean_mk_array(v_nbuckets_220_, v___x_222_);
v___x_224_ = lean_array_propagate_mark(v_data_217_, v___x_223_);
v___x_225_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4___redArg(v___x_221_, v_data_217_, v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__4___redArg(lean_object* v_a_226_, lean_object* v_b_227_, lean_object* v_x_228_){
_start:
{
if (lean_obj_tag(v_x_228_) == 0)
{
lean_dec(v_b_227_);
lean_dec_ref(v_a_226_);
return v_x_228_;
}
else
{
lean_object* v_key_229_; lean_object* v_value_230_; lean_object* v_tail_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_245_; 
v_key_229_ = lean_ctor_get(v_x_228_, 0);
v_value_230_ = lean_ctor_get(v_x_228_, 1);
v_tail_231_ = lean_ctor_get(v_x_228_, 2);
v_isSharedCheck_245_ = !lean_is_exclusive(v_x_228_);
if (v_isSharedCheck_245_ == 0)
{
v___x_233_ = v_x_228_;
v_isShared_234_ = v_isSharedCheck_245_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_tail_231_);
lean_inc(v_value_230_);
lean_inc(v_key_229_);
lean_dec(v_x_228_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_245_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
size_t v___x_235_; size_t v___x_236_; uint8_t v___x_237_; 
v___x_235_ = lean_ptr_addr(v_key_229_);
v___x_236_ = lean_ptr_addr(v_a_226_);
v___x_237_ = lean_usize_dec_eq(v___x_235_, v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_238_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__4___redArg(v_a_226_, v_b_227_, v_tail_231_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 2, v___x_238_);
v___x_240_ = v___x_233_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_key_229_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_value_230_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
else
{
lean_object* v___x_243_; 
lean_dec(v_value_230_);
lean_dec(v_key_229_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v_b_227_);
lean_ctor_set(v___x_233_, 0, v_a_226_);
v___x_243_ = v___x_233_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_226_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_b_227_);
lean_ctor_set(v_reuseFailAlloc_244_, 2, v_tail_231_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___redArg(lean_object* v_a_246_, lean_object* v_x_247_){
_start:
{
if (lean_obj_tag(v_x_247_) == 0)
{
uint8_t v___x_248_; 
v___x_248_ = 0;
return v___x_248_;
}
else
{
lean_object* v_key_249_; lean_object* v_tail_250_; size_t v___x_251_; size_t v___x_252_; uint8_t v___x_253_; 
v_key_249_ = lean_ctor_get(v_x_247_, 0);
v_tail_250_ = lean_ctor_get(v_x_247_, 2);
v___x_251_ = lean_ptr_addr(v_key_249_);
v___x_252_ = lean_ptr_addr(v_a_246_);
v___x_253_ = lean_usize_dec_eq(v___x_251_, v___x_252_);
if (v___x_253_ == 0)
{
v_x_247_ = v_tail_250_;
goto _start;
}
else
{
return v___x_253_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_246_ = stack[0].m_obj;
lean_object* v_x_247_ = stack[1].m_obj;
uint8_t v_res_255_;
v_res_255_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___redArg(v_a_246_, v_x_247_);
stack->m_num = v_res_255_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___redArg___boxed(lean_object* v_a_256_, lean_object* v_x_257_){
_start:
{
uint8_t v_res_258_; lean_object* v_r_259_; 
v_res_258_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___redArg(v_a_256_, v_x_257_);
lean_dec(v_x_257_);
lean_dec_ref(v_a_256_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(lean_object* v_m_260_, lean_object* v_a_261_, lean_object* v_b_262_){
_start:
{
lean_object* v_size_263_; lean_object* v_buckets_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_310_; 
v_size_263_ = lean_ctor_get(v_m_260_, 0);
v_buckets_264_ = lean_ctor_get(v_m_260_, 1);
v_isSharedCheck_310_ = !lean_is_exclusive(v_m_260_);
if (v_isSharedCheck_310_ == 0)
{
v___x_266_ = v_m_260_;
v_isShared_267_ = v_isSharedCheck_310_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_buckets_264_);
lean_inc(v_size_263_);
lean_dec(v_m_260_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_310_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; size_t v___x_269_; size_t v___x_270_; size_t v___x_271_; uint64_t v___x_272_; uint64_t v___x_273_; uint64_t v___x_274_; uint64_t v_fold_275_; uint64_t v___x_276_; uint64_t v___x_277_; uint64_t v___x_278_; size_t v___x_279_; size_t v___x_280_; size_t v___x_281_; size_t v___x_282_; size_t v___x_283_; lean_object* v_bkt_284_; uint8_t v___x_285_; 
v___x_268_ = lean_array_get_size(v_buckets_264_);
v___x_269_ = lean_ptr_addr(v_a_261_);
v___x_270_ = ((size_t)3ULL);
v___x_271_ = lean_usize_shift_right(v___x_269_, v___x_270_);
v___x_272_ = lean_usize_to_uint64(v___x_271_);
v___x_273_ = 32ULL;
v___x_274_ = lean_uint64_shift_right(v___x_272_, v___x_273_);
v_fold_275_ = lean_uint64_xor(v___x_272_, v___x_274_);
v___x_276_ = 16ULL;
v___x_277_ = lean_uint64_shift_right(v_fold_275_, v___x_276_);
v___x_278_ = lean_uint64_xor(v_fold_275_, v___x_277_);
v___x_279_ = lean_uint64_to_usize(v___x_278_);
v___x_280_ = lean_usize_of_nat(v___x_268_);
v___x_281_ = ((size_t)1ULL);
v___x_282_ = lean_usize_sub(v___x_280_, v___x_281_);
v___x_283_ = lean_usize_land(v___x_279_, v___x_282_);
v_bkt_284_ = lean_array_uget_borrowed(v_buckets_264_, v___x_283_);
v___x_285_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___redArg(v_a_261_, v_bkt_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v_size_x27_287_; lean_object* v___x_288_; lean_object* v_buckets_x27_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_286_ = lean_unsigned_to_nat(1u);
v_size_x27_287_ = lean_nat_add(v_size_263_, v___x_286_);
lean_dec(v_size_263_);
lean_inc(v_bkt_284_);
v___x_288_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_288_, 0, v_a_261_);
lean_ctor_set(v___x_288_, 1, v_b_262_);
lean_ctor_set(v___x_288_, 2, v_bkt_284_);
v_buckets_x27_289_ = lean_array_uset(v_buckets_264_, v___x_283_, v___x_288_);
v___x_290_ = lean_unsigned_to_nat(4u);
v___x_291_ = lean_nat_mul(v_size_x27_287_, v___x_290_);
v___x_292_ = lean_unsigned_to_nat(3u);
v___x_293_ = lean_nat_div(v___x_291_, v___x_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_array_get_size(v_buckets_x27_289_);
v___x_295_ = lean_nat_dec_le(v___x_293_, v___x_294_);
lean_dec(v___x_293_);
if (v___x_295_ == 0)
{
lean_object* v_val_296_; lean_object* v___x_298_; 
v_val_296_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3___redArg(v_buckets_x27_289_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 1, v_val_296_);
lean_ctor_set(v___x_266_, 0, v_size_x27_287_);
v___x_298_ = v___x_266_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_size_x27_287_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_val_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
else
{
lean_object* v___x_301_; 
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 1, v_buckets_x27_289_);
lean_ctor_set(v___x_266_, 0, v_size_x27_287_);
v___x_301_ = v___x_266_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_size_x27_287_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_buckets_x27_289_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
else
{
lean_object* v___x_303_; lean_object* v_buckets_x27_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
lean_inc(v_bkt_284_);
v___x_303_ = lean_box(0);
v_buckets_x27_304_ = lean_array_uset(v_buckets_264_, v___x_283_, v___x_303_);
v___x_305_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__4___redArg(v_a_261_, v_b_262_, v_bkt_284_);
v___x_306_ = lean_array_uset(v_buckets_x27_304_, v___x_283_, v___x_305_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 1, v___x_306_);
v___x_308_ = v___x_266_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_size_263_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v___x_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___redArg(lean_object* v_a_311_, lean_object* v_x_312_){
_start:
{
if (lean_obj_tag(v_x_312_) == 0)
{
lean_object* v___x_313_; 
v___x_313_ = lean_box(0);
return v___x_313_;
}
else
{
lean_object* v_key_314_; lean_object* v_value_315_; lean_object* v_tail_316_; size_t v___x_317_; size_t v___x_318_; uint8_t v___x_319_; 
v_key_314_ = lean_ctor_get(v_x_312_, 0);
v_value_315_ = lean_ctor_get(v_x_312_, 1);
v_tail_316_ = lean_ctor_get(v_x_312_, 2);
v___x_317_ = lean_ptr_addr(v_key_314_);
v___x_318_ = lean_ptr_addr(v_a_311_);
v___x_319_ = lean_usize_dec_eq(v___x_317_, v___x_318_);
if (v___x_319_ == 0)
{
v_x_312_ = v_tail_316_;
goto _start;
}
else
{
lean_object* v___x_321_; 
lean_inc(v_value_315_);
v___x_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_321_, 0, v_value_315_);
return v___x_321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___redArg___boxed(lean_object* v_a_322_, lean_object* v_x_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___redArg(v_a_322_, v_x_323_);
lean_dec(v_x_323_);
lean_dec_ref(v_a_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(lean_object* v_m_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_buckets_327_; lean_object* v___x_328_; size_t v___x_329_; size_t v___x_330_; size_t v___x_331_; uint64_t v___x_332_; uint64_t v___x_333_; uint64_t v___x_334_; uint64_t v_fold_335_; uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v___x_338_; size_t v___x_339_; size_t v___x_340_; size_t v___x_341_; size_t v___x_342_; size_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_buckets_327_ = lean_ctor_get(v_m_325_, 1);
v___x_328_ = lean_array_get_size(v_buckets_327_);
v___x_329_ = lean_ptr_addr(v_a_326_);
v___x_330_ = ((size_t)3ULL);
v___x_331_ = lean_usize_shift_right(v___x_329_, v___x_330_);
v___x_332_ = lean_usize_to_uint64(v___x_331_);
v___x_333_ = 32ULL;
v___x_334_ = lean_uint64_shift_right(v___x_332_, v___x_333_);
v_fold_335_ = lean_uint64_xor(v___x_332_, v___x_334_);
v___x_336_ = 16ULL;
v___x_337_ = lean_uint64_shift_right(v_fold_335_, v___x_336_);
v___x_338_ = lean_uint64_xor(v_fold_335_, v___x_337_);
v___x_339_ = lean_uint64_to_usize(v___x_338_);
v___x_340_ = lean_usize_of_nat(v___x_328_);
v___x_341_ = ((size_t)1ULL);
v___x_342_ = lean_usize_sub(v___x_340_, v___x_341_);
v___x_343_ = lean_usize_land(v___x_339_, v___x_342_);
v___x_344_ = lean_array_uget_borrowed(v_buckets_327_, v___x_343_);
v___x_345_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___redArg(v_a_326_, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg___boxed(lean_object* v_m_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_m_346_, v_a_347_);
lean_dec_ref(v_a_347_);
lean_dec_ref(v_m_346_);
return v_res_348_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(lean_object* v_e_349_, lean_object* v_k_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_360_; lean_object* v_hasDepLetCache_361_; lean_object* v___x_362_; 
v___x_360_ = lean_st_ref_get(v_a_352_);
v_hasDepLetCache_361_ = lean_ctor_get(v___x_360_, 4);
lean_inc_ref(v_hasDepLetCache_361_);
lean_dec(v___x_360_);
v___x_362_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_hasDepLetCache_361_, v_e_349_);
lean_dec_ref(v_hasDepLetCache_361_);
if (lean_obj_tag(v___x_362_) == 1)
{
lean_object* v_val_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
lean_dec_ref(v_k_350_);
lean_dec_ref(v_e_349_);
v_val_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_val_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set_tag(v___x_365_, 0);
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_val_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
else
{
lean_object* v___x_371_; 
lean_dec(v___x_362_);
lean_inc(v_a_358_);
lean_inc_ref(v_a_357_);
lean_inc(v_a_356_);
lean_inc_ref(v_a_355_);
lean_inc(v_a_354_);
lean_inc_ref(v_a_353_);
lean_inc(v_a_352_);
lean_inc_ref(v_a_351_);
v___x_371_ = lean_apply_9(v_k_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, lean_box(0));
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_395_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_395_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_395_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_395_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v_visited_377_; lean_object* v_types_378_; lean_object* v_subst_379_; lean_object* v_visitedClosed_380_; lean_object* v_hasDepLetCache_381_; lean_object* v_numConverted_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_394_; 
v___x_376_ = lean_st_ref_take(v_a_352_);
v_visited_377_ = lean_ctor_get(v___x_376_, 0);
v_types_378_ = lean_ctor_get(v___x_376_, 1);
v_subst_379_ = lean_ctor_get(v___x_376_, 2);
v_visitedClosed_380_ = lean_ctor_get(v___x_376_, 3);
v_hasDepLetCache_381_ = lean_ctor_get(v___x_376_, 4);
v_numConverted_382_ = lean_ctor_get(v___x_376_, 5);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_394_ == 0)
{
v___x_384_ = v___x_376_;
v_isShared_385_ = v_isSharedCheck_394_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_numConverted_382_);
lean_inc(v_hasDepLetCache_381_);
lean_inc(v_visitedClosed_380_);
lean_inc(v_subst_379_);
lean_inc(v_types_378_);
lean_inc(v_visited_377_);
lean_dec(v___x_376_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_394_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_388_; 
lean_inc(v_a_372_);
v___x_386_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_hasDepLetCache_381_, v_e_349_, v_a_372_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 4, v___x_386_);
v___x_388_ = v___x_384_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_visited_377_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_types_378_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v_subst_379_);
lean_ctor_set(v_reuseFailAlloc_393_, 3, v_visitedClosed_380_);
lean_ctor_set(v_reuseFailAlloc_393_, 4, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_393_, 5, v_numConverted_382_);
v___x_388_ = v_reuseFailAlloc_393_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_389_ = lean_st_ref_put(v_a_352_, v___x_388_);
if (v_isShared_375_ == 0)
{
v___x_391_ = v___x_374_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_372_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_349_);
return v___x_371_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_349_ = stack[0].m_obj;
lean_object* v_k_350_ = stack[1].m_obj;
lean_object* v_a_351_ = stack[2].m_obj;
lean_object* v_a_352_ = stack[3].m_obj;
lean_object* v_a_353_ = stack[4].m_obj;
lean_object* v_a_354_ = stack[5].m_obj;
lean_object* v_a_355_ = stack[6].m_obj;
lean_object* v_a_356_ = stack[7].m_obj;
lean_object* v_a_357_ = stack[8].m_obj;
lean_object* v_a_358_ = stack[9].m_obj;
lean_object* v_res_396_;
v_res_396_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(v_e_349_, v_k_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
stack->m_obj
 = v_res_396_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached___boxed(lean_object* v_e_397_, lean_object* v_k_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(v_e_397_, v_k_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0(lean_object* v_00_u03b2_409_, lean_object* v_m_410_, lean_object* v_a_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_m_410_, v_a_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___boxed(lean_object* v_00_u03b2_413_, lean_object* v_m_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0(v_00_u03b2_413_, v_m_414_, v_a_415_);
lean_dec_ref(v_a_415_);
lean_dec_ref(v_m_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1(lean_object* v_00_u03b2_417_, lean_object* v_m_418_, lean_object* v_a_419_, lean_object* v_b_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_m_418_, v_a_419_, v_b_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0(lean_object* v_00_u03b2_422_, lean_object* v_a_423_, lean_object* v_x_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___redArg(v_a_423_, v_x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_426_, lean_object* v_a_427_, lean_object* v_x_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0_spec__0(v_00_u03b2_426_, v_a_427_, v_x_428_);
lean_dec(v_x_428_);
lean_dec_ref(v_a_427_);
return v_res_429_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2(lean_object* v_00_u03b2_430_, lean_object* v_a_431_, lean_object* v_x_432_){
_start:
{
uint8_t v___x_433_; 
v___x_433_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___redArg(v_a_431_, v_x_432_);
return v___x_433_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_431_ = stack[1].m_obj;
lean_object* v_x_432_ = stack[2].m_obj;
uint8_t v_res_434_;
v_res_434_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2(lean_box(0), v_a_431_, v_x_432_);
stack->m_num = v_res_434_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2___boxed(lean_object* v_00_u03b2_435_, lean_object* v_a_436_, lean_object* v_x_437_){
_start:
{
uint8_t v_res_438_; lean_object* v_r_439_; 
v_res_438_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__2(v_00_u03b2_435_, v_a_436_, v_x_437_);
lean_dec(v_x_437_);
lean_dec_ref(v_a_436_);
v_r_439_ = lean_box(v_res_438_);
return v_r_439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3(lean_object* v_00_u03b2_440_, lean_object* v_data_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3___redArg(v_data_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__4(lean_object* v_00_u03b2_443_, lean_object* v_a_444_, lean_object* v_b_445_, lean_object* v_x_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__4___redArg(v_a_444_, v_b_445_, v_x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_448_, lean_object* v_i_449_, lean_object* v_source_450_, lean_object* v_target_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4___redArg(v_i_449_, v_source_450_, v_target_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_453_, lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1_spec__3_spec__4_spec__5___redArg(v_x_454_, v_x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__0___boxed(lean_object* v_t_457_, lean_object* v_b_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__0(v_t_457_, v_b_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
return v_res_468_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__1(lean_object* v_type_469_, lean_object* v_value_470_, lean_object* v_body_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_type_469_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; uint8_t v___x_483_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v___x_483_ = lean_unbox(v_a_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
lean_dec_ref_known(v___x_481_, 1);
v___x_484_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_value_470_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; uint8_t v___x_486_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
v___x_486_ = lean_unbox(v_a_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
lean_dec_ref_known(v___x_484_, 1);
v___x_487_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_body_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
return v___x_487_;
}
else
{
lean_dec_ref(v_body_471_);
return v___x_484_;
}
}
else
{
lean_dec_ref(v_body_471_);
return v___x_484_;
}
}
else
{
lean_dec_ref(v_body_471_);
lean_dec_ref(v_value_470_);
return v___x_481_;
}
}
else
{
lean_dec_ref(v_body_471_);
lean_dec_ref(v_value_470_);
return v___x_481_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_469_ = stack[0].m_obj;
lean_object* v_value_470_ = stack[1].m_obj;
lean_object* v_body_471_ = stack[2].m_obj;
lean_object* v___y_472_ = stack[3].m_obj;
lean_object* v___y_473_ = stack[4].m_obj;
lean_object* v___y_474_ = stack[5].m_obj;
lean_object* v___y_475_ = stack[6].m_obj;
lean_object* v___y_476_ = stack[7].m_obj;
lean_object* v___y_477_ = stack[8].m_obj;
lean_object* v___y_478_ = stack[9].m_obj;
lean_object* v___y_479_ = stack[10].m_obj;
lean_object* v_res_488_;
v_res_488_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__1(v_type_469_, v_value_470_, v_body_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
stack->m_obj
 = v_res_488_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__1___boxed(lean_object* v_type_489_, lean_object* v_value_490_, lean_object* v_body_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__1(v_type_489_, v_value_490_, v_body_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
return v_res_501_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__2(lean_object* v_fn_502_, lean_object* v_arg_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_fn_502_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; uint8_t v___x_515_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v___x_515_ = lean_unbox(v_a_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; 
lean_dec_ref_known(v___x_513_, 1);
v___x_516_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_arg_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
return v___x_516_;
}
else
{
lean_dec_ref(v_arg_503_);
return v___x_513_;
}
}
else
{
lean_dec_ref(v_arg_503_);
return v___x_513_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_502_ = stack[0].m_obj;
lean_object* v_arg_503_ = stack[1].m_obj;
lean_object* v___y_504_ = stack[2].m_obj;
lean_object* v___y_505_ = stack[3].m_obj;
lean_object* v___y_506_ = stack[4].m_obj;
lean_object* v___y_507_ = stack[5].m_obj;
lean_object* v___y_508_ = stack[6].m_obj;
lean_object* v___y_509_ = stack[7].m_obj;
lean_object* v___y_510_ = stack[8].m_obj;
lean_object* v___y_511_ = stack[9].m_obj;
lean_object* v_res_517_;
v_res_517_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__2(v_fn_502_, v_arg_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
stack->m_obj
 = v_res_517_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__2___boxed(lean_object* v_fn_518_, lean_object* v_arg_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__2(v_fn_518_, v_arg_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___boxed(lean_object* v_e_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_e_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
return v_res_540_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(lean_object* v_e_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_t_552_; lean_object* v_b_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; 
switch(lean_obj_tag(v_e_541_))
{
case 8:
{
uint8_t v_nondep_564_; 
v_nondep_564_ = lean_ctor_get_uint8(v_e_541_, sizeof(void*)*4 + 8);
if (v_nondep_564_ == 0)
{
uint8_t v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec_ref_known(v_e_541_, 4);
v___x_565_ = 1;
v___x_566_ = lean_box(v___x_565_);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
else
{
lean_object* v_type_568_; lean_object* v_value_569_; lean_object* v_body_570_; lean_object* v___f_571_; lean_object* v___x_572_; 
v_type_568_ = lean_ctor_get(v_e_541_, 1);
v_value_569_ = lean_ctor_get(v_e_541_, 2);
v_body_570_ = lean_ctor_get(v_e_541_, 3);
lean_inc_ref(v_body_570_);
lean_inc_ref(v_value_569_);
lean_inc_ref(v_type_568_);
v___f_571_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__1___boxed), 12, 3);
lean_closure_set(v___f_571_, 0, v_type_568_);
lean_closure_set(v___f_571_, 1, v_value_569_);
lean_closure_set(v___f_571_, 2, v_body_570_);
v___x_572_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(v_e_541_, v___f_571_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
return v___x_572_;
}
}
case 5:
{
lean_object* v_fn_573_; lean_object* v_arg_574_; lean_object* v___f_575_; lean_object* v___x_576_; 
v_fn_573_ = lean_ctor_get(v_e_541_, 0);
v_arg_574_ = lean_ctor_get(v_e_541_, 1);
lean_inc_ref(v_arg_574_);
lean_inc_ref(v_fn_573_);
v___f_575_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__2___boxed), 11, 2);
lean_closure_set(v___f_575_, 0, v_fn_573_);
lean_closure_set(v___f_575_, 1, v_arg_574_);
v___x_576_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(v_e_541_, v___f_575_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
return v___x_576_;
}
case 6:
{
lean_object* v_binderType_577_; lean_object* v_body_578_; 
v_binderType_577_ = lean_ctor_get(v_e_541_, 1);
v_body_578_ = lean_ctor_get(v_e_541_, 2);
lean_inc_ref(v_body_578_);
lean_inc_ref(v_binderType_577_);
v_t_552_ = v_binderType_577_;
v_b_553_ = v_body_578_;
v___y_554_ = v_a_542_;
v___y_555_ = v_a_543_;
v___y_556_ = v_a_544_;
v___y_557_ = v_a_545_;
v___y_558_ = v_a_546_;
v___y_559_ = v_a_547_;
v___y_560_ = v_a_548_;
v___y_561_ = v_a_549_;
goto v___jp_551_;
}
case 7:
{
lean_object* v_binderType_579_; lean_object* v_body_580_; 
v_binderType_579_ = lean_ctor_get(v_e_541_, 1);
v_body_580_ = lean_ctor_get(v_e_541_, 2);
lean_inc_ref(v_body_580_);
lean_inc_ref(v_binderType_579_);
v_t_552_ = v_binderType_579_;
v_b_553_ = v_body_580_;
v___y_554_ = v_a_542_;
v___y_555_ = v_a_543_;
v___y_556_ = v_a_544_;
v___y_557_ = v_a_545_;
v___y_558_ = v_a_546_;
v___y_559_ = v_a_547_;
v___y_560_ = v_a_548_;
v___y_561_ = v_a_549_;
goto v___jp_551_;
}
case 10:
{
lean_object* v_expr_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_expr_581_ = lean_ctor_get(v_e_541_, 1);
lean_inc_ref(v_expr_581_);
v___x_582_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___boxed), 10, 1);
lean_closure_set(v___x_582_, 0, v_expr_581_);
v___x_583_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(v_e_541_, v___x_582_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
return v___x_583_;
}
case 11:
{
lean_object* v_struct_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_struct_584_ = lean_ctor_get(v_e_541_, 2);
lean_inc_ref(v_struct_584_);
v___x_585_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___boxed), 10, 1);
lean_closure_set(v___x_585_, 0, v_struct_584_);
v___x_586_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(v_e_541_, v___x_585_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
return v___x_586_;
}
default: 
{
uint8_t v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
lean_dec_ref(v_e_541_);
v___x_587_ = 0;
v___x_588_ = lean_box(v___x_587_);
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
return v___x_589_;
}
}
v___jp_551_:
{
lean_object* v___f_562_; lean_object* v___x_563_; 
v___f_562_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__0___boxed), 11, 2);
lean_closure_set(v___f_562_, 0, v_t_552_);
lean_closure_set(v___f_562_, 1, v_b_553_);
v___x_563_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached(v_e_541_, v___f_562_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
return v___x_563_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_541_ = stack[0].m_obj;
lean_object* v_a_542_ = stack[1].m_obj;
lean_object* v_a_543_ = stack[2].m_obj;
lean_object* v_a_544_ = stack[3].m_obj;
lean_object* v_a_545_ = stack[4].m_obj;
lean_object* v_a_546_ = stack[5].m_obj;
lean_object* v_a_547_ = stack[6].m_obj;
lean_object* v_a_548_ = stack[7].m_obj;
lean_object* v_a_549_ = stack[8].m_obj;
lean_object* v_res_590_;
v_res_590_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_e_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
stack->m_obj
 = v_res_590_;
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__0(lean_object* v_t_591_, lean_object* v_b_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_t_591_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; uint8_t v___x_604_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v___x_604_ = lean_unbox(v_a_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
lean_dec_ref_known(v___x_602_, 1);
v___x_605_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_b_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
return v___x_605_;
}
else
{
lean_dec_ref(v_b_592_);
return v___x_602_;
}
}
else
{
lean_dec_ref(v_b_592_);
return v___x_602_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_591_ = stack[0].m_obj;
lean_object* v_b_592_ = stack[1].m_obj;
lean_object* v___y_593_ = stack[2].m_obj;
lean_object* v___y_594_ = stack[3].m_obj;
lean_object* v___y_595_ = stack[4].m_obj;
lean_object* v___y_596_ = stack[5].m_obj;
lean_object* v___y_597_ = stack[6].m_obj;
lean_object* v___y_598_ = stack[7].m_obj;
lean_object* v___y_599_ = stack[8].m_obj;
lean_object* v___y_600_ = stack[9].m_obj;
lean_object* v_res_606_;
v_res_606_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet___lam__0(v_t_591_, v_b_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
stack->m_obj
 = v_res_606_;
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___closed__0(void){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_607_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1(lean_object* v_msg_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_10876__overap_617_; lean_object* v___x_618_; 
v___x_616_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___closed__0);
v___x_10876__overap_617_ = lean_panic_fn_borrowed(v___x_616_, v_msg_608_);
lean_inc(v___y_614_);
lean_inc_ref(v___y_613_);
lean_inc(v___y_612_);
lean_inc_ref(v___y_611_);
lean_inc(v___y_610_);
lean_inc_ref(v___y_609_);
v___x_618_ = lean_apply_7(v___x_10876__overap_617_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, lean_box(0));
return v___x_618_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_608_ = stack[0].m_obj;
lean_object* v___y_609_ = stack[1].m_obj;
lean_object* v___y_610_ = stack[2].m_obj;
lean_object* v___y_611_ = stack[3].m_obj;
lean_object* v___y_612_ = stack[4].m_obj;
lean_object* v___y_613_ = stack[5].m_obj;
lean_object* v___y_614_ = stack[6].m_obj;
lean_object* v_res_619_;
v_res_619_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1(v_msg_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
stack->m_obj
 = v_res_619_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___boxed(lean_object* v_msg_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1(v_msg_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
return v_res_628_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1(lean_object* v_f_629_, lean_object* v_a_630_, lean_object* v___y_631_, uint8_t v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v___y_636_; lean_object* v___y_637_; 
if (v___y_632_ == 0)
{
v___y_636_ = v___y_631_;
v___y_637_ = v___y_634_;
goto v___jp_635_;
}
else
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_629_, v___y_632_, v___y_633_, v___y_634_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_661_; 
v_a_660_ = lean_ctor_get(v___x_659_, 1);
lean_inc(v_a_660_);
lean_dec_ref_known(v___x_659_, 2);
v___x_661_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_630_, v___y_632_, v___y_633_, v_a_660_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; 
v_a_662_ = lean_ctor_get(v___x_661_, 1);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 2);
v___y_636_ = v___y_631_;
v___y_637_ = v_a_662_;
goto v___jp_635_;
}
else
{
lean_object* v_a_663_; lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec_ref(v___y_631_);
lean_dec_ref(v_a_630_);
lean_dec_ref(v_f_629_);
v_a_663_ = lean_ctor_get(v___x_661_, 0);
v_a_664_ = lean_ctor_get(v___x_661_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_661_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_inc(v_a_663_);
lean_dec(v___x_661_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_663_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
else
{
lean_object* v_a_672_; lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref(v___y_631_);
lean_dec_ref(v_a_630_);
lean_dec_ref(v_f_629_);
v_a_672_ = lean_ctor_get(v___x_659_, 0);
v_a_673_ = lean_ctor_get(v___x_659_, 1);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_659_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_inc(v_a_672_);
lean_dec(v___x_659_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_672_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
v___jp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = l_Lean_Expr_app___override(v_f_629_, v_a_630_);
v___x_639_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_638_, v___y_637_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_649_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_a_641_ = lean_ctor_get(v___x_639_, 1);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_649_ == 0)
{
v___x_643_ = v___x_639_;
v_isShared_644_ = v_isSharedCheck_649_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_649_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v_a_640_);
lean_ctor_set(v___x_645_, 1, v___y_636_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_645_);
v___x_647_ = v___x_643_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_a_641_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
else
{
lean_object* v_a_650_; lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec_ref(v___y_636_);
v_a_650_ = lean_ctor_get(v___x_639_, 0);
v_a_651_ = lean_ctor_get(v___x_639_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_639_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_inc(v_a_650_);
lean_dec(v___x_639_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_650_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_629_ = stack[0].m_obj;
lean_object* v_a_630_ = stack[1].m_obj;
lean_object* v___y_631_ = stack[2].m_obj;
uint8_t v___y_632_ = stack[3].m_num;
lean_object* v___y_633_ = stack[4].m_obj;
lean_object* v___y_634_ = stack[5].m_obj;
lean_object* v_res_681_;
v_res_681_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1(v_f_629_, v_a_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
stack->m_obj
 = v_res_681_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1___boxed(lean_object* v_f_682_, lean_object* v_a_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
uint8_t v___y_33907__boxed_688_; lean_object* v_res_689_; 
v___y_33907__boxed_688_ = lean_unbox(v___y_685_);
v_res_689_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1(v_f_682_, v_a_683_, v___y_684_, v___y_33907__boxed_688_, v___y_686_, v___y_687_);
lean_dec_ref(v___y_686_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(lean_object* v_a_690_, lean_object* v_x_691_){
_start:
{
if (lean_obj_tag(v_x_691_) == 0)
{
lean_object* v___x_692_; 
v___x_692_ = lean_box(0);
return v___x_692_;
}
else
{
lean_object* v_key_693_; lean_object* v_value_694_; lean_object* v_tail_695_; lean_object* v_fst_696_; lean_object* v_snd_697_; lean_object* v_fst_698_; lean_object* v_snd_699_; size_t v___x_700_; size_t v___x_701_; uint8_t v___x_702_; 
v_key_693_ = lean_ctor_get(v_x_691_, 0);
v_value_694_ = lean_ctor_get(v_x_691_, 1);
v_tail_695_ = lean_ctor_get(v_x_691_, 2);
v_fst_696_ = lean_ctor_get(v_key_693_, 0);
v_snd_697_ = lean_ctor_get(v_key_693_, 1);
v_fst_698_ = lean_ctor_get(v_a_690_, 0);
v_snd_699_ = lean_ctor_get(v_a_690_, 1);
v___x_700_ = lean_ptr_addr(v_fst_696_);
v___x_701_ = lean_ptr_addr(v_fst_698_);
v___x_702_ = lean_usize_dec_eq(v___x_700_, v___x_701_);
if (v___x_702_ == 0)
{
v_x_691_ = v_tail_695_;
goto _start;
}
else
{
uint8_t v___x_704_; 
v___x_704_ = lean_nat_dec_eq(v_snd_697_, v_snd_699_);
if (v___x_704_ == 0)
{
v_x_691_ = v_tail_695_;
goto _start;
}
else
{
lean_object* v___x_706_; 
lean_inc(v_value_694_);
v___x_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_706_, 0, v_value_694_);
return v___x_706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_a_707_, lean_object* v_x_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_707_, v_x_708_);
lean_dec(v_x_708_);
lean_dec_ref(v_a_707_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___redArg(lean_object* v_m_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_buckets_712_; lean_object* v_fst_713_; lean_object* v_snd_714_; lean_object* v___x_715_; size_t v___x_716_; size_t v___x_717_; size_t v___x_718_; uint64_t v___x_719_; uint64_t v___x_720_; uint64_t v___x_721_; uint64_t v___x_722_; uint64_t v___x_723_; uint64_t v_fold_724_; uint64_t v___x_725_; uint64_t v___x_726_; uint64_t v___x_727_; size_t v___x_728_; size_t v___x_729_; size_t v___x_730_; size_t v___x_731_; size_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_buckets_712_ = lean_ctor_get(v_m_710_, 1);
v_fst_713_ = lean_ctor_get(v_a_711_, 0);
v_snd_714_ = lean_ctor_get(v_a_711_, 1);
v___x_715_ = lean_array_get_size(v_buckets_712_);
v___x_716_ = lean_ptr_addr(v_fst_713_);
v___x_717_ = ((size_t)3ULL);
v___x_718_ = lean_usize_shift_right(v___x_716_, v___x_717_);
v___x_719_ = lean_usize_to_uint64(v___x_718_);
v___x_720_ = lean_uint64_of_nat(v_snd_714_);
v___x_721_ = lean_uint64_mix_hash(v___x_719_, v___x_720_);
v___x_722_ = 32ULL;
v___x_723_ = lean_uint64_shift_right(v___x_721_, v___x_722_);
v_fold_724_ = lean_uint64_xor(v___x_721_, v___x_723_);
v___x_725_ = 16ULL;
v___x_726_ = lean_uint64_shift_right(v_fold_724_, v___x_725_);
v___x_727_ = lean_uint64_xor(v_fold_724_, v___x_726_);
v___x_728_ = lean_uint64_to_usize(v___x_727_);
v___x_729_ = lean_usize_of_nat(v___x_715_);
v___x_730_ = ((size_t)1ULL);
v___x_731_ = lean_usize_sub(v___x_729_, v___x_730_);
v___x_732_ = lean_usize_land(v___x_728_, v___x_731_);
v___x_733_ = lean_array_uget_borrowed(v_buckets_712_, v___x_732_);
v___x_734_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_711_, v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___redArg(v_m_735_, v_a_736_);
lean_dec_ref(v_a_736_);
lean_dec_ref(v_m_735_);
return v_res_737_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7(lean_object* v_msg_745_, lean_object* v___y_746_, uint8_t v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___f_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___f_762_; lean_object* v___f_763_; lean_object* v___f_764_; lean_object* v___f_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_33404__overap_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___f_750_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__0));
v___f_751_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__1));
v___f_752_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__2));
v___x_753_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__3));
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v___f_750_);
v___x_755_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__4));
v___x_756_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__5));
v___x_757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_757_, 0, v___x_754_);
lean_ctor_set(v___x_757_, 1, v___x_755_);
lean_ctor_set(v___x_757_, 2, v___f_751_);
lean_ctor_set(v___x_757_, 3, v___f_752_);
lean_ctor_set(v___x_757_, 4, v___x_756_);
v___x_758_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__6));
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_757_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = l_ReaderT_instMonad___redArg(v___x_759_);
v___x_761_ = l_ReaderT_instMonad___redArg(v___x_760_);
lean_inc_ref_n(v___x_761_, 6);
v___f_762_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_762_, 0, v___x_761_);
v___f_763_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_763_, 0, v___x_761_);
v___f_764_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_764_, 0, v___x_761_);
v___f_765_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_765_, 0, v___x_761_);
v___x_766_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_766_, 0, lean_box(0));
lean_closure_set(v___x_766_, 1, lean_box(0));
lean_closure_set(v___x_766_, 2, v___x_761_);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v___f_762_);
v___x_768_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_768_, 0, lean_box(0));
lean_closure_set(v___x_768_, 1, lean_box(0));
lean_closure_set(v___x_768_, 2, v___x_761_);
v___x_769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
lean_ctor_set(v___x_769_, 2, v___f_763_);
lean_ctor_set(v___x_769_, 3, v___f_764_);
lean_ctor_set(v___x_769_, 4, v___f_765_);
v___x_770_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_770_, 0, lean_box(0));
lean_closure_set(v___x_770_, 1, lean_box(0));
lean_closure_set(v___x_770_, 2, v___x_761_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_769_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = l_Lean_instInhabitedExpr;
v___x_773_ = l_instInhabitedOfMonad___redArg(v___x_771_, v___x_772_);
v___x_33404__overap_774_ = lean_panic_fn_borrowed(v___x_773_, v_msg_745_);
lean_dec(v___x_773_);
v___x_775_ = lean_box(v___y_747_);
lean_inc_ref(v___y_748_);
v___x_776_ = lean_apply_4(v___x_33404__overap_774_, v___y_746_, v___x_775_, v___y_748_, v___y_749_);
return v___x_776_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_745_ = stack[0].m_obj;
lean_object* v___y_746_ = stack[1].m_obj;
uint8_t v___y_747_ = stack[2].m_num;
lean_object* v___y_748_ = stack[3].m_obj;
lean_object* v___y_749_ = stack[4].m_obj;
lean_object* v_res_777_;
v_res_777_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7(v_msg_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
stack->m_obj
 = v_res_777_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___boxed(lean_object* v_msg_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
uint8_t v___y_34197__boxed_783_; lean_object* v_res_784_; 
v___y_34197__boxed_783_ = lean_unbox(v___y_780_);
v_res_784_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7(v_msg_778_, v___y_779_, v___y_34197__boxed_783_, v___y_781_, v___y_782_);
lean_dec_ref(v___y_781_);
return v_res_784_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__6(lean_object* v_structName_785_, lean_object* v_idx_786_, lean_object* v_struct_787_, lean_object* v___y_788_, uint8_t v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___y_793_; lean_object* v___y_794_; 
if (v___y_789_ == 0)
{
v___y_793_ = v___y_788_;
v___y_794_ = v___y_791_;
goto v___jp_792_;
}
else
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_787_, v___y_789_, v___y_790_, v___y_791_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; 
v_a_817_ = lean_ctor_get(v___x_816_, 1);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_816_, 2);
v___y_793_ = v___y_788_;
v___y_794_ = v_a_817_;
goto v___jp_792_;
}
else
{
lean_object* v_a_818_; lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref(v___y_788_);
lean_dec_ref(v_struct_787_);
lean_dec(v_idx_786_);
lean_dec(v_structName_785_);
v_a_818_ = lean_ctor_get(v___x_816_, 0);
v_a_819_ = lean_ctor_get(v___x_816_, 1);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_816_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_inc(v_a_818_);
lean_dec(v___x_816_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_818_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
v___jp_792_:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = l_Lean_Expr_proj___override(v_structName_785_, v_idx_786_, v_struct_787_);
v___x_796_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_795_, v___y_794_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_806_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
v_a_798_ = lean_ctor_get(v___x_796_, 1);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_806_ == 0)
{
v___x_800_ = v___x_796_;
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_inc(v_a_797_);
lean_dec(v___x_796_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v_a_797_);
lean_ctor_set(v___x_802_, 1, v___y_793_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_802_);
v___x_804_ = v___x_800_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_a_798_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
else
{
lean_object* v_a_807_; lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v___y_793_);
v_a_807_ = lean_ctor_get(v___x_796_, 0);
v_a_808_ = lean_ctor_get(v___x_796_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_796_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_inc(v_a_807_);
lean_dec(v___x_796_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_807_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_structName_785_ = stack[0].m_obj;
lean_object* v_idx_786_ = stack[1].m_obj;
lean_object* v_struct_787_ = stack[2].m_obj;
lean_object* v___y_788_ = stack[3].m_obj;
uint8_t v___y_789_ = stack[4].m_num;
lean_object* v___y_790_ = stack[5].m_obj;
lean_object* v___y_791_ = stack[6].m_obj;
lean_object* v_res_827_;
v_res_827_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__6(v_structName_785_, v_idx_786_, v_struct_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
stack->m_obj
 = v_res_827_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__6___boxed(lean_object* v_structName_828_, lean_object* v_idx_829_, lean_object* v_struct_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
uint8_t v___y_34309__boxed_835_; lean_object* v_res_836_; 
v___y_34309__boxed_835_ = lean_unbox(v___y_832_);
v_res_836_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__6(v_structName_828_, v_idx_829_, v_struct_830_, v___y_831_, v___y_34309__boxed_835_, v___y_833_, v___y_834_);
lean_dec_ref(v___y_833_);
return v_res_836_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4(lean_object* v_x_837_, lean_object* v_t_838_, lean_object* v_v_839_, lean_object* v_b_840_, uint8_t v_nondep_841_, lean_object* v___y_842_, uint8_t v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___y_847_; lean_object* v___y_848_; 
if (v___y_843_ == 0)
{
v___y_847_ = v___y_842_;
v___y_848_ = v___y_845_;
goto v___jp_846_;
}
else
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_838_, v___y_843_, v___y_844_, v___y_845_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_872_; 
v_a_871_ = lean_ctor_get(v___x_870_, 1);
lean_inc(v_a_871_);
lean_dec_ref_known(v___x_870_, 2);
v___x_872_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_839_, v___y_843_, v___y_844_, v_a_871_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_874_; 
v_a_873_ = lean_ctor_get(v___x_872_, 1);
lean_inc(v_a_873_);
lean_dec_ref_known(v___x_872_, 2);
v___x_874_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_840_, v___y_843_, v___y_844_, v_a_873_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; 
v_a_875_ = lean_ctor_get(v___x_874_, 1);
lean_inc(v_a_875_);
lean_dec_ref_known(v___x_874_, 2);
v___y_847_ = v___y_842_;
v___y_848_ = v_a_875_;
goto v___jp_846_;
}
else
{
lean_object* v_a_876_; lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_dec_ref(v___y_842_);
lean_dec_ref(v_b_840_);
lean_dec_ref(v_v_839_);
lean_dec_ref(v_t_838_);
lean_dec(v_x_837_);
v_a_876_ = lean_ctor_get(v___x_874_, 0);
v_a_877_ = lean_ctor_get(v___x_874_, 1);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_874_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_inc(v_a_876_);
lean_dec(v___x_874_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_876_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
else
{
lean_object* v_a_885_; lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec_ref(v___y_842_);
lean_dec_ref(v_b_840_);
lean_dec_ref(v_v_839_);
lean_dec_ref(v_t_838_);
lean_dec(v_x_837_);
v_a_885_ = lean_ctor_get(v___x_872_, 0);
v_a_886_ = lean_ctor_get(v___x_872_, 1);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_872_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_inc(v_a_885_);
lean_dec(v___x_872_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_885_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec_ref(v___y_842_);
lean_dec_ref(v_b_840_);
lean_dec_ref(v_v_839_);
lean_dec_ref(v_t_838_);
lean_dec(v_x_837_);
v_a_894_ = lean_ctor_get(v___x_870_, 0);
v_a_895_ = lean_ctor_get(v___x_870_, 1);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_870_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_inc(v_a_894_);
lean_dec(v___x_870_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_894_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
v___jp_846_:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = l_Lean_Expr_letE___override(v_x_837_, v_t_838_, v_v_839_, v_b_840_, v_nondep_841_);
v___x_850_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_849_, v___y_848_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_860_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_a_852_ = lean_ctor_get(v___x_850_, 1);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_860_ == 0)
{
v___x_854_ = v___x_850_;
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v_a_851_);
lean_ctor_set(v___x_856_, 1, v___y_847_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_856_);
v___x_858_ = v___x_854_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_a_852_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
else
{
lean_object* v_a_861_; lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec_ref(v___y_847_);
v_a_861_ = lean_ctor_get(v___x_850_, 0);
v_a_862_ = lean_ctor_get(v___x_850_, 1);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_850_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_inc(v_a_861_);
lean_dec(v___x_850_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_861_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_837_ = stack[0].m_obj;
lean_object* v_t_838_ = stack[1].m_obj;
lean_object* v_v_839_ = stack[2].m_obj;
lean_object* v_b_840_ = stack[3].m_obj;
uint8_t v_nondep_841_ = stack[4].m_num;
lean_object* v___y_842_ = stack[5].m_obj;
uint8_t v___y_843_ = stack[6].m_num;
lean_object* v___y_844_ = stack[7].m_obj;
lean_object* v___y_845_ = stack[8].m_obj;
lean_object* v_res_903_;
v_res_903_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4(v_x_837_, v_t_838_, v_v_839_, v_b_840_, v_nondep_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
stack->m_obj
 = v_res_903_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4___boxed(lean_object* v_x_904_, lean_object* v_t_905_, lean_object* v_v_906_, lean_object* v_b_907_, lean_object* v_nondep_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
uint8_t v_nondep_boxed_913_; uint8_t v___y_34435__boxed_914_; lean_object* v_res_915_; 
v_nondep_boxed_913_ = lean_unbox(v_nondep_908_);
v___y_34435__boxed_914_ = lean_unbox(v___y_910_);
v_res_915_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4(v_x_904_, v_t_905_, v_v_906_, v_b_907_, v_nondep_boxed_913_, v___y_909_, v___y_34435__boxed_914_, v___y_911_, v___y_912_);
lean_dec_ref(v___y_911_);
return v_res_915_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2(lean_object* v_x_916_, uint8_t v_bi_917_, lean_object* v_t_918_, lean_object* v_b_919_, lean_object* v___y_920_, uint8_t v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___y_925_; lean_object* v___y_926_; 
if (v___y_921_ == 0)
{
v___y_925_ = v___y_920_;
v___y_926_ = v___y_923_;
goto v___jp_924_;
}
else
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_918_, v___y_921_, v___y_922_, v___y_923_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_950_; 
v_a_949_ = lean_ctor_get(v___x_948_, 1);
lean_inc(v_a_949_);
lean_dec_ref_known(v___x_948_, 2);
v___x_950_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_919_, v___y_921_, v___y_922_, v_a_949_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; 
v_a_951_ = lean_ctor_get(v___x_950_, 1);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 2);
v___y_925_ = v___y_920_;
v___y_926_ = v_a_951_;
goto v___jp_924_;
}
else
{
lean_object* v_a_952_; lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec_ref(v___y_920_);
lean_dec_ref(v_b_919_);
lean_dec_ref(v_t_918_);
lean_dec(v_x_916_);
v_a_952_ = lean_ctor_get(v___x_950_, 0);
v_a_953_ = lean_ctor_get(v___x_950_, 1);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_950_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_inc(v_a_952_);
lean_dec(v___x_950_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_952_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
else
{
lean_object* v_a_961_; lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_dec_ref(v___y_920_);
lean_dec_ref(v_b_919_);
lean_dec_ref(v_t_918_);
lean_dec(v_x_916_);
v_a_961_ = lean_ctor_get(v___x_948_, 0);
v_a_962_ = lean_ctor_get(v___x_948_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_948_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_inc(v_a_961_);
lean_dec(v___x_948_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_961_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
v___jp_924_:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = l_Lean_Expr_lam___override(v_x_916_, v_t_918_, v_b_919_, v_bi_917_);
v___x_928_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_927_, v___y_926_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_938_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
v_a_930_ = lean_ctor_get(v___x_928_, 1);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_938_ == 0)
{
v___x_932_ = v___x_928_;
v_isShared_933_ = v_isSharedCheck_938_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_inc(v_a_929_);
lean_dec(v___x_928_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_938_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_a_929_);
lean_ctor_set(v___x_934_, 1, v___y_925_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_934_);
v___x_936_ = v___x_932_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_a_930_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
else
{
lean_object* v_a_939_; lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref(v___y_925_);
v_a_939_ = lean_ctor_get(v___x_928_, 0);
v_a_940_ = lean_ctor_get(v___x_928_, 1);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_928_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_inc(v_a_939_);
lean_dec(v___x_928_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_939_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_916_ = stack[0].m_obj;
uint8_t v_bi_917_ = stack[1].m_num;
lean_object* v_t_918_ = stack[2].m_obj;
lean_object* v_b_919_ = stack[3].m_obj;
lean_object* v___y_920_ = stack[4].m_obj;
uint8_t v___y_921_ = stack[5].m_num;
lean_object* v___y_922_ = stack[6].m_obj;
lean_object* v___y_923_ = stack[7].m_obj;
lean_object* v_res_970_;
v_res_970_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2(v_x_916_, v_bi_917_, v_t_918_, v_b_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
stack->m_obj
 = v_res_970_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2___boxed(lean_object* v_x_971_, lean_object* v_bi_972_, lean_object* v_t_973_, lean_object* v_b_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
uint8_t v_bi_boxed_979_; uint8_t v___y_34629__boxed_980_; lean_object* v_res_981_; 
v_bi_boxed_979_ = lean_unbox(v_bi_972_);
v___y_34629__boxed_980_ = lean_unbox(v___y_976_);
v_res_981_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2(v_x_971_, v_bi_boxed_979_, v_t_973_, v_b_974_, v___y_975_, v___y_34629__boxed_980_, v___y_977_, v___y_978_);
lean_dec_ref(v___y_977_);
return v_res_981_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__5(lean_object* v_d_982_, lean_object* v_e_983_, lean_object* v___y_984_, uint8_t v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___y_989_; lean_object* v___y_990_; 
if (v___y_985_ == 0)
{
v___y_989_ = v___y_984_;
v___y_990_ = v___y_987_;
goto v___jp_988_;
}
else
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_983_, v___y_985_, v___y_986_, v___y_987_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 1);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1012_, 2);
v___y_989_ = v___y_984_;
v___y_990_ = v_a_1013_;
goto v___jp_988_;
}
else
{
lean_object* v_a_1014_; lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec_ref(v___y_984_);
lean_dec_ref(v_e_983_);
lean_dec(v_d_982_);
v_a_1014_ = lean_ctor_get(v___x_1012_, 0);
v_a_1015_ = lean_ctor_get(v___x_1012_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1012_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_inc(v_a_1014_);
lean_dec(v___x_1012_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1014_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
v___jp_988_:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = l_Lean_Expr_mdata___override(v_d_982_, v_e_983_);
v___x_992_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_991_, v___y_990_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1002_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_a_994_ = lean_ctor_get(v___x_992_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_996_ = v___x_992_;
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_998_, 0, v_a_993_);
lean_ctor_set(v___x_998_, 1, v___y_989_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_998_);
v___x_1000_ = v___x_996_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_a_994_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v___y_989_);
v_a_1003_ = lean_ctor_get(v___x_992_, 0);
v_a_1004_ = lean_ctor_get(v___x_992_, 1);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_992_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_inc(v_a_1003_);
lean_dec(v___x_992_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1003_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_982_ = stack[0].m_obj;
lean_object* v_e_983_ = stack[1].m_obj;
lean_object* v___y_984_ = stack[2].m_obj;
uint8_t v___y_985_ = stack[3].m_num;
lean_object* v___y_986_ = stack[4].m_obj;
lean_object* v___y_987_ = stack[5].m_obj;
lean_object* v_res_1023_;
v_res_1023_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__5(v_d_982_, v_e_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
stack->m_obj
 = v_res_1023_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__5___boxed(lean_object* v_d_1024_, lean_object* v_e_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
uint8_t v___y_34789__boxed_1030_; lean_object* v_res_1031_; 
v___y_34789__boxed_1030_ = lean_unbox(v___y_1027_);
v_res_1031_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__5(v_d_1024_, v_e_1025_, v___y_1026_, v___y_34789__boxed_1030_, v___y_1028_, v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1031_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3(lean_object* v_x_1032_, uint8_t v_bi_1033_, lean_object* v_t_1034_, lean_object* v_b_1035_, lean_object* v___y_1036_, uint8_t v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___y_1041_; lean_object* v___y_1042_; 
if (v___y_1037_ == 0)
{
v___y_1041_ = v___y_1036_;
v___y_1042_ = v___y_1039_;
goto v___jp_1040_;
}
else
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1034_, v___y_1037_, v___y_1038_, v___y_1039_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1066_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 1);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 2);
v___x_1066_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1035_, v___y_1037_, v___y_1038_, v_a_1065_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 1);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 2);
v___y_1041_ = v___y_1036_;
v___y_1042_ = v_a_1067_;
goto v___jp_1040_;
}
else
{
lean_object* v_a_1068_; lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec_ref(v___y_1036_);
lean_dec_ref(v_b_1035_);
lean_dec_ref(v_t_1034_);
lean_dec(v_x_1032_);
v_a_1068_ = lean_ctor_get(v___x_1066_, 0);
v_a_1069_ = lean_ctor_get(v___x_1066_, 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1066_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_inc(v_a_1068_);
lean_dec(v___x_1066_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1068_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec_ref(v___y_1036_);
lean_dec_ref(v_b_1035_);
lean_dec_ref(v_t_1034_);
lean_dec(v_x_1032_);
v_a_1077_ = lean_ctor_get(v___x_1064_, 0);
v_a_1078_ = lean_ctor_get(v___x_1064_, 1);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1064_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_inc(v_a_1077_);
lean_dec(v___x_1064_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1077_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_a_1078_);
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
v___jp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = l_Lean_Expr_forallE___override(v_x_1032_, v_t_1034_, v_b_1035_, v_bi_1033_);
v___x_1044_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1043_, v___y_1042_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1054_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
v_a_1046_ = lean_ctor_get(v___x_1044_, 1);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1048_ = v___x_1044_;
v_isShared_1049_ = v_isSharedCheck_1054_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_inc(v_a_1045_);
lean_dec(v___x_1044_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1054_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1050_, 0, v_a_1045_);
lean_ctor_set(v___x_1050_, 1, v___y_1041_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1050_);
v___x_1052_ = v___x_1048_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_a_1046_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec_ref(v___y_1041_);
v_a_1055_ = lean_ctor_get(v___x_1044_, 0);
v_a_1056_ = lean_ctor_get(v___x_1044_, 1);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1044_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_inc(v_a_1055_);
lean_dec(v___x_1044_);
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
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1055_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_a_1056_);
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
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1032_ = stack[0].m_obj;
uint8_t v_bi_1033_ = stack[1].m_num;
lean_object* v_t_1034_ = stack[2].m_obj;
lean_object* v_b_1035_ = stack[3].m_obj;
lean_object* v___y_1036_ = stack[4].m_obj;
uint8_t v___y_1037_ = stack[5].m_num;
lean_object* v___y_1038_ = stack[6].m_obj;
lean_object* v___y_1039_ = stack[7].m_obj;
lean_object* v_res_1086_;
v_res_1086_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3(v_x_1032_, v_bi_1033_, v_t_1034_, v_b_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
stack->m_obj
 = v_res_1086_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3___boxed(lean_object* v_x_1087_, lean_object* v_bi_1088_, lean_object* v_t_1089_, lean_object* v_b_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
uint8_t v_bi_boxed_1095_; uint8_t v___y_34915__boxed_1096_; lean_object* v_res_1097_; 
v_bi_boxed_1095_ = lean_unbox(v_bi_1088_);
v___y_34915__boxed_1096_ = lean_unbox(v___y_1092_);
v_res_1097_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3(v_x_1087_, v_bi_boxed_1095_, v_t_1089_, v_b_1090_, v___y_1091_, v___y_34915__boxed_1096_, v___y_1093_, v___y_1094_);
lean_dec_ref(v___y_1093_);
return v_res_1097_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1101_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_1102_ = lean_unsigned_to_nat(67u);
v___x_1103_ = lean_unsigned_to_nat(35u);
v___x_1104_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__1));
v___x_1105_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__0));
v___x_1106_ = l_mkPanicMessageWithDecl(v___x_1105_, v___x_1104_, v___x_1103_, v___x_1102_, v___x_1101_);
return v___x_1106_;
}
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0(lean_object* v___x_1107_, lean_object* v___x_1108_, lean_object* v_e_1109_, lean_object* v_offset_1110_, lean_object* v_a_1111_, uint8_t v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
switch(lean_obj_tag(v_e_1109_))
{
case 5:
{
lean_object* v_fn_1115_; lean_object* v_arg_1116_; lean_object* v___x_1117_; 
v_fn_1115_ = lean_ctor_get(v_e_1109_, 0);
v_arg_1116_ = lean_ctor_get(v_e_1109_, 1);
lean_inc(v_offset_1110_);
lean_inc_ref(v_fn_1115_);
v___x_1117_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1107_, v___x_1108_, v_fn_1115_, v_offset_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v_a_1119_; lean_object* v_fst_1120_; lean_object* v_snd_1121_; lean_object* v___x_1122_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
v_a_1119_ = lean_ctor_get(v___x_1117_, 1);
lean_inc(v_a_1119_);
lean_dec_ref_known(v___x_1117_, 2);
v_fst_1120_ = lean_ctor_get(v_a_1118_, 0);
lean_inc(v_fst_1120_);
v_snd_1121_ = lean_ctor_get(v_a_1118_, 1);
lean_inc(v_snd_1121_);
lean_dec(v_a_1118_);
lean_inc_ref(v_arg_1116_);
v___x_1122_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1107_, v___x_1108_, v_arg_1116_, v_offset_1110_, v_snd_1121_, v_a_1112_, v_a_1113_, v_a_1119_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1148_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
v_a_1124_ = lean_ctor_get(v___x_1122_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1126_ = v___x_1122_;
v_isShared_1127_ = v_isSharedCheck_1148_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_inc(v_a_1123_);
lean_dec(v___x_1122_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1148_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v_fst_1128_; lean_object* v_snd_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1147_; 
v_fst_1128_ = lean_ctor_get(v_a_1123_, 0);
v_snd_1129_ = lean_ctor_get(v_a_1123_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_a_1123_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1131_ = v_a_1123_;
v_isShared_1132_ = v_isSharedCheck_1147_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_snd_1129_);
lean_inc(v_fst_1128_);
lean_dec(v_a_1123_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1147_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
size_t v___x_1133_; size_t v___x_1134_; uint8_t v___x_1135_; 
v___x_1133_ = lean_ptr_addr(v_fn_1115_);
v___x_1134_ = lean_ptr_addr(v_fst_1120_);
v___x_1135_ = lean_usize_dec_eq(v___x_1133_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; 
lean_del_object(v___x_1131_);
lean_del_object(v___x_1126_);
lean_dec_ref_known(v_e_1109_, 2);
v___x_1136_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1(v_fst_1120_, v_fst_1128_, v_snd_1129_, v_a_1112_, v_a_1113_, v_a_1124_);
return v___x_1136_;
}
else
{
size_t v___x_1137_; size_t v___x_1138_; uint8_t v___x_1139_; 
v___x_1137_ = lean_ptr_addr(v_arg_1116_);
v___x_1138_ = lean_ptr_addr(v_fst_1128_);
v___x_1139_ = lean_usize_dec_eq(v___x_1137_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; 
lean_del_object(v___x_1131_);
lean_del_object(v___x_1126_);
lean_dec_ref_known(v_e_1109_, 2);
v___x_1140_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1(v_fst_1120_, v_fst_1128_, v_snd_1129_, v_a_1112_, v_a_1113_, v_a_1124_);
return v___x_1140_;
}
else
{
lean_object* v___x_1142_; 
lean_dec(v_fst_1128_);
lean_dec(v_fst_1120_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v_e_1109_);
v___x_1142_ = v___x_1131_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_e_1109_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_snd_1129_);
v___x_1142_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1144_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1142_);
v___x_1144_ = v___x_1126_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_a_1124_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1120_);
lean_dec_ref_known(v_e_1109_, 2);
return v___x_1122_;
}
}
else
{
lean_dec_ref_known(v_e_1109_, 2);
lean_dec(v_offset_1110_);
return v___x_1117_;
}
}
case 6:
{
lean_object* v_binderName_1149_; lean_object* v_binderType_1150_; lean_object* v_body_1151_; uint8_t v_binderInfo_1152_; lean_object* v___x_1153_; 
v_binderName_1149_ = lean_ctor_get(v_e_1109_, 0);
v_binderType_1150_ = lean_ctor_get(v_e_1109_, 1);
v_body_1151_ = lean_ctor_get(v_e_1109_, 2);
v_binderInfo_1152_ = lean_ctor_get_uint8(v_e_1109_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1110_);
lean_inc_ref(v_binderType_1150_);
v___x_1153_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1107_, v___x_1108_, v_binderType_1150_, v_offset_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v_a_1155_; lean_object* v_fst_1156_; lean_object* v_snd_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_a_1154_);
v_a_1155_ = lean_ctor_get(v___x_1153_, 1);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1153_, 2);
v_fst_1156_ = lean_ctor_get(v_a_1154_, 0);
lean_inc(v_fst_1156_);
v_snd_1157_ = lean_ctor_get(v_a_1154_, 1);
lean_inc(v_snd_1157_);
lean_dec(v_a_1154_);
v___x_1158_ = lean_unsigned_to_nat(1u);
v___x_1159_ = lean_nat_add(v_offset_1110_, v___x_1158_);
lean_dec(v_offset_1110_);
lean_inc_ref(v_body_1151_);
v___x_1160_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1107_, v___x_1108_, v_body_1151_, v___x_1159_, v_snd_1157_, v_a_1112_, v_a_1113_, v_a_1155_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1186_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
v_a_1162_ = lean_ctor_get(v___x_1160_, 1);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1164_ = v___x_1160_;
v_isShared_1165_ = v_isSharedCheck_1186_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_inc(v_a_1161_);
lean_dec(v___x_1160_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1186_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v_fst_1166_; lean_object* v_snd_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1185_; 
v_fst_1166_ = lean_ctor_get(v_a_1161_, 0);
v_snd_1167_ = lean_ctor_get(v_a_1161_, 1);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_a_1161_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1169_ = v_a_1161_;
v_isShared_1170_ = v_isSharedCheck_1185_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_snd_1167_);
lean_inc(v_fst_1166_);
lean_dec(v_a_1161_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1185_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
size_t v___x_1171_; size_t v___x_1172_; uint8_t v___x_1173_; 
v___x_1171_ = lean_ptr_addr(v_binderType_1150_);
v___x_1172_ = lean_ptr_addr(v_fst_1156_);
v___x_1173_ = lean_usize_dec_eq(v___x_1171_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; 
lean_inc(v_binderName_1149_);
lean_del_object(v___x_1169_);
lean_del_object(v___x_1164_);
lean_dec_ref_known(v_e_1109_, 3);
v___x_1174_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2(v_binderName_1149_, v_binderInfo_1152_, v_fst_1156_, v_fst_1166_, v_snd_1167_, v_a_1112_, v_a_1113_, v_a_1162_);
return v___x_1174_;
}
else
{
size_t v___x_1175_; size_t v___x_1176_; uint8_t v___x_1177_; 
v___x_1175_ = lean_ptr_addr(v_body_1151_);
v___x_1176_ = lean_ptr_addr(v_fst_1166_);
v___x_1177_ = lean_usize_dec_eq(v___x_1175_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; 
lean_inc(v_binderName_1149_);
lean_del_object(v___x_1169_);
lean_del_object(v___x_1164_);
lean_dec_ref_known(v_e_1109_, 3);
v___x_1178_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2(v_binderName_1149_, v_binderInfo_1152_, v_fst_1156_, v_fst_1166_, v_snd_1167_, v_a_1112_, v_a_1113_, v_a_1162_);
return v___x_1178_;
}
else
{
lean_object* v___x_1180_; 
lean_dec(v_fst_1166_);
lean_dec(v_fst_1156_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v_e_1109_);
v___x_1180_ = v___x_1169_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_e_1109_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_snd_1167_);
v___x_1180_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1182_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1180_);
v___x_1182_ = v___x_1164_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_a_1162_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1156_);
lean_dec_ref_known(v_e_1109_, 3);
return v___x_1160_;
}
}
else
{
lean_dec_ref_known(v_e_1109_, 3);
lean_dec(v_offset_1110_);
return v___x_1153_;
}
}
case 7:
{
lean_object* v_binderName_1187_; lean_object* v_binderType_1188_; lean_object* v_body_1189_; uint8_t v_binderInfo_1190_; lean_object* v___x_1191_; 
v_binderName_1187_ = lean_ctor_get(v_e_1109_, 0);
v_binderType_1188_ = lean_ctor_get(v_e_1109_, 1);
v_body_1189_ = lean_ctor_get(v_e_1109_, 2);
v_binderInfo_1190_ = lean_ctor_get_uint8(v_e_1109_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1110_);
lean_inc_ref(v_binderType_1188_);
v___x_1191_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1107_, v___x_1108_, v_binderType_1188_, v_offset_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v_a_1193_; lean_object* v_fst_1194_; lean_object* v_snd_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1192_);
v_a_1193_ = lean_ctor_get(v___x_1191_, 1);
lean_inc(v_a_1193_);
lean_dec_ref_known(v___x_1191_, 2);
v_fst_1194_ = lean_ctor_get(v_a_1192_, 0);
lean_inc(v_fst_1194_);
v_snd_1195_ = lean_ctor_get(v_a_1192_, 1);
lean_inc(v_snd_1195_);
lean_dec(v_a_1192_);
v___x_1196_ = lean_unsigned_to_nat(1u);
v___x_1197_ = lean_nat_add(v_offset_1110_, v___x_1196_);
lean_dec(v_offset_1110_);
lean_inc_ref(v_body_1189_);
v___x_1198_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1107_, v___x_1108_, v_body_1189_, v___x_1197_, v_snd_1195_, v_a_1112_, v_a_1113_, v_a_1193_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1224_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_a_1200_ = lean_ctor_get(v___x_1198_, 1);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1202_ = v___x_1198_;
v_isShared_1203_ = v_isSharedCheck_1224_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1224_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v_fst_1204_; lean_object* v_snd_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1223_; 
v_fst_1204_ = lean_ctor_get(v_a_1199_, 0);
v_snd_1205_ = lean_ctor_get(v_a_1199_, 1);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_a_1199_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1207_ = v_a_1199_;
v_isShared_1208_ = v_isSharedCheck_1223_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_snd_1205_);
lean_inc(v_fst_1204_);
lean_dec(v_a_1199_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1223_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
size_t v___x_1209_; size_t v___x_1210_; uint8_t v___x_1211_; 
v___x_1209_ = lean_ptr_addr(v_binderType_1188_);
v___x_1210_ = lean_ptr_addr(v_fst_1194_);
v___x_1211_ = lean_usize_dec_eq(v___x_1209_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; 
lean_inc(v_binderName_1187_);
lean_del_object(v___x_1207_);
lean_del_object(v___x_1202_);
lean_dec_ref_known(v_e_1109_, 3);
v___x_1212_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3(v_binderName_1187_, v_binderInfo_1190_, v_fst_1194_, v_fst_1204_, v_snd_1205_, v_a_1112_, v_a_1113_, v_a_1200_);
return v___x_1212_;
}
else
{
size_t v___x_1213_; size_t v___x_1214_; uint8_t v___x_1215_; 
v___x_1213_ = lean_ptr_addr(v_body_1189_);
v___x_1214_ = lean_ptr_addr(v_fst_1204_);
v___x_1215_ = lean_usize_dec_eq(v___x_1213_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; 
lean_inc(v_binderName_1187_);
lean_del_object(v___x_1207_);
lean_del_object(v___x_1202_);
lean_dec_ref_known(v_e_1109_, 3);
v___x_1216_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3(v_binderName_1187_, v_binderInfo_1190_, v_fst_1194_, v_fst_1204_, v_snd_1205_, v_a_1112_, v_a_1113_, v_a_1200_);
return v___x_1216_;
}
else
{
lean_object* v___x_1218_; 
lean_dec(v_fst_1204_);
lean_dec(v_fst_1194_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v_e_1109_);
v___x_1218_ = v___x_1207_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_e_1109_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_snd_1205_);
v___x_1218_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1220_; 
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1218_);
v___x_1220_ = v___x_1202_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_a_1200_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1194_);
lean_dec_ref_known(v_e_1109_, 3);
return v___x_1198_;
}
}
else
{
lean_dec_ref_known(v_e_1109_, 3);
lean_dec(v_offset_1110_);
return v___x_1191_;
}
}
case 8:
{
lean_object* v_declName_1225_; lean_object* v_type_1226_; lean_object* v_value_1227_; lean_object* v_body_1228_; uint8_t v_nondep_1229_; lean_object* v___x_1230_; 
v_declName_1225_ = lean_ctor_get(v_e_1109_, 0);
v_type_1226_ = lean_ctor_get(v_e_1109_, 1);
v_value_1227_ = lean_ctor_get(v_e_1109_, 2);
v_body_1228_ = lean_ctor_get(v_e_1109_, 3);
v_nondep_1229_ = lean_ctor_get_uint8(v_e_1109_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1110_);
lean_inc_ref(v_type_1226_);
v___x_1230_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1107_, v___x_1108_, v_type_1226_, v_offset_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v_a_1232_; lean_object* v_fst_1233_; lean_object* v_snd_1234_; lean_object* v___x_1235_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1231_);
v_a_1232_ = lean_ctor_get(v___x_1230_, 1);
lean_inc(v_a_1232_);
lean_dec_ref_known(v___x_1230_, 2);
v_fst_1233_ = lean_ctor_get(v_a_1231_, 0);
lean_inc(v_fst_1233_);
v_snd_1234_ = lean_ctor_get(v_a_1231_, 1);
lean_inc(v_snd_1234_);
lean_dec(v_a_1231_);
lean_inc(v_offset_1110_);
lean_inc_ref(v_value_1227_);
v___x_1235_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1107_, v___x_1108_, v_value_1227_, v_offset_1110_, v_snd_1234_, v_a_1112_, v_a_1113_, v_a_1232_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v_a_1237_; lean_object* v_fst_1238_; lean_object* v_snd_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1236_);
v_a_1237_ = lean_ctor_get(v___x_1235_, 1);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___x_1235_, 2);
v_fst_1238_ = lean_ctor_get(v_a_1236_, 0);
lean_inc(v_fst_1238_);
v_snd_1239_ = lean_ctor_get(v_a_1236_, 1);
lean_inc(v_snd_1239_);
lean_dec(v_a_1236_);
v___x_1240_ = lean_unsigned_to_nat(1u);
v___x_1241_ = lean_nat_add(v_offset_1110_, v___x_1240_);
lean_dec(v_offset_1110_);
lean_inc_ref(v_body_1228_);
v___x_1242_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1107_, v___x_1108_, v_body_1228_, v___x_1241_, v_snd_1239_, v_a_1112_, v_a_1113_, v_a_1237_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1272_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
v_a_1244_ = lean_ctor_get(v___x_1242_, 1);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1246_ = v___x_1242_;
v_isShared_1247_ = v_isSharedCheck_1272_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_inc(v_a_1243_);
lean_dec(v___x_1242_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1272_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v_fst_1248_; lean_object* v_snd_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1271_; 
v_fst_1248_ = lean_ctor_get(v_a_1243_, 0);
v_snd_1249_ = lean_ctor_get(v_a_1243_, 1);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_a_1243_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1251_ = v_a_1243_;
v_isShared_1252_ = v_isSharedCheck_1271_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_snd_1249_);
lean_inc(v_fst_1248_);
lean_dec(v_a_1243_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1271_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
size_t v___x_1253_; size_t v___x_1254_; uint8_t v___x_1255_; 
v___x_1253_ = lean_ptr_addr(v_type_1226_);
v___x_1254_ = lean_ptr_addr(v_fst_1233_);
v___x_1255_ = lean_usize_dec_eq(v___x_1253_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
lean_inc(v_declName_1225_);
lean_del_object(v___x_1251_);
lean_del_object(v___x_1246_);
lean_dec_ref_known(v_e_1109_, 4);
v___x_1256_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4(v_declName_1225_, v_fst_1233_, v_fst_1238_, v_fst_1248_, v_nondep_1229_, v_snd_1249_, v_a_1112_, v_a_1113_, v_a_1244_);
return v___x_1256_;
}
else
{
size_t v___x_1257_; size_t v___x_1258_; uint8_t v___x_1259_; 
v___x_1257_ = lean_ptr_addr(v_value_1227_);
v___x_1258_ = lean_ptr_addr(v_fst_1238_);
v___x_1259_ = lean_usize_dec_eq(v___x_1257_, v___x_1258_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; 
lean_inc(v_declName_1225_);
lean_del_object(v___x_1251_);
lean_del_object(v___x_1246_);
lean_dec_ref_known(v_e_1109_, 4);
v___x_1260_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4(v_declName_1225_, v_fst_1233_, v_fst_1238_, v_fst_1248_, v_nondep_1229_, v_snd_1249_, v_a_1112_, v_a_1113_, v_a_1244_);
return v___x_1260_;
}
else
{
size_t v___x_1261_; size_t v___x_1262_; uint8_t v___x_1263_; 
v___x_1261_ = lean_ptr_addr(v_body_1228_);
v___x_1262_ = lean_ptr_addr(v_fst_1248_);
v___x_1263_ = lean_usize_dec_eq(v___x_1261_, v___x_1262_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; 
lean_inc(v_declName_1225_);
lean_del_object(v___x_1251_);
lean_del_object(v___x_1246_);
lean_dec_ref_known(v_e_1109_, 4);
v___x_1264_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4(v_declName_1225_, v_fst_1233_, v_fst_1238_, v_fst_1248_, v_nondep_1229_, v_snd_1249_, v_a_1112_, v_a_1113_, v_a_1244_);
return v___x_1264_;
}
else
{
lean_object* v___x_1266_; 
lean_dec(v_fst_1248_);
lean_dec(v_fst_1238_);
lean_dec(v_fst_1233_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v_e_1109_);
v___x_1266_ = v___x_1251_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_e_1109_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_snd_1249_);
v___x_1266_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1268_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1266_);
v___x_1268_ = v___x_1246_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_a_1244_);
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
}
}
}
else
{
lean_dec(v_fst_1238_);
lean_dec(v_fst_1233_);
lean_dec_ref_known(v_e_1109_, 4);
return v___x_1242_;
}
}
else
{
lean_dec(v_fst_1233_);
lean_dec_ref_known(v_e_1109_, 4);
lean_dec(v_offset_1110_);
return v___x_1235_;
}
}
else
{
lean_dec_ref_known(v_e_1109_, 4);
lean_dec(v_offset_1110_);
return v___x_1230_;
}
}
case 10:
{
lean_object* v_data_1273_; lean_object* v_expr_1274_; lean_object* v___x_1275_; 
v_data_1273_ = lean_ctor_get(v_e_1109_, 0);
v_expr_1274_ = lean_ctor_get(v_e_1109_, 1);
lean_inc_ref(v_expr_1274_);
v___x_1275_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1107_, v___x_1108_, v_expr_1274_, v_offset_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1297_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_a_1277_ = lean_ctor_get(v___x_1275_, 1);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1279_ = v___x_1275_;
v_isShared_1280_ = v_isSharedCheck_1297_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1297_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v_fst_1281_; lean_object* v_snd_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1296_; 
v_fst_1281_ = lean_ctor_get(v_a_1276_, 0);
v_snd_1282_ = lean_ctor_get(v_a_1276_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_a_1276_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1284_ = v_a_1276_;
v_isShared_1285_ = v_isSharedCheck_1296_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_snd_1282_);
lean_inc(v_fst_1281_);
lean_dec(v_a_1276_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1296_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
size_t v___x_1286_; size_t v___x_1287_; uint8_t v___x_1288_; 
v___x_1286_ = lean_ptr_addr(v_expr_1274_);
v___x_1287_ = lean_ptr_addr(v_fst_1281_);
v___x_1288_ = lean_usize_dec_eq(v___x_1286_, v___x_1287_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; 
lean_inc(v_data_1273_);
lean_del_object(v___x_1284_);
lean_del_object(v___x_1279_);
lean_dec_ref_known(v_e_1109_, 2);
v___x_1289_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__5(v_data_1273_, v_fst_1281_, v_snd_1282_, v_a_1112_, v_a_1113_, v_a_1277_);
return v___x_1289_;
}
else
{
lean_object* v___x_1291_; 
lean_dec(v_fst_1281_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v_e_1109_);
v___x_1291_ = v___x_1284_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_e_1109_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_snd_1282_);
v___x_1291_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_object* v___x_1293_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1291_);
v___x_1293_ = v___x_1279_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_a_1277_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1109_, 2);
return v___x_1275_;
}
}
case 11:
{
lean_object* v_typeName_1298_; lean_object* v_idx_1299_; lean_object* v_struct_1300_; lean_object* v___x_1301_; 
v_typeName_1298_ = lean_ctor_get(v_e_1109_, 0);
v_idx_1299_ = lean_ctor_get(v_e_1109_, 1);
v_struct_1300_ = lean_ctor_get(v_e_1109_, 2);
lean_inc_ref(v_struct_1300_);
v___x_1301_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1107_, v___x_1108_, v_struct_1300_, v_offset_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1323_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v_a_1303_ = lean_ctor_get(v___x_1301_, 1);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1305_ = v___x_1301_;
v_isShared_1306_ = v_isSharedCheck_1323_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_inc(v_a_1302_);
lean_dec(v___x_1301_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1323_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v_fst_1307_; lean_object* v_snd_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1322_; 
v_fst_1307_ = lean_ctor_get(v_a_1302_, 0);
v_snd_1308_ = lean_ctor_get(v_a_1302_, 1);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_a_1302_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1310_ = v_a_1302_;
v_isShared_1311_ = v_isSharedCheck_1322_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_snd_1308_);
lean_inc(v_fst_1307_);
lean_dec(v_a_1302_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1322_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
size_t v___x_1312_; size_t v___x_1313_; uint8_t v___x_1314_; 
v___x_1312_ = lean_ptr_addr(v_struct_1300_);
v___x_1313_ = lean_ptr_addr(v_fst_1307_);
v___x_1314_ = lean_usize_dec_eq(v___x_1312_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; 
lean_inc(v_idx_1299_);
lean_inc(v_typeName_1298_);
lean_del_object(v___x_1310_);
lean_del_object(v___x_1305_);
lean_dec_ref_known(v_e_1109_, 3);
v___x_1315_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__6(v_typeName_1298_, v_idx_1299_, v_fst_1307_, v_snd_1308_, v_a_1112_, v_a_1113_, v_a_1303_);
return v___x_1315_;
}
else
{
lean_object* v___x_1317_; 
lean_dec(v_fst_1307_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v_e_1109_);
v___x_1317_ = v___x_1310_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_e_1109_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_snd_1308_);
v___x_1317_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1319_; 
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v___x_1317_);
v___x_1319_ = v___x_1305_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_a_1303_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1109_, 3);
return v___x_1301_;
}
}
default: 
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_dec(v_offset_1110_);
lean_dec_ref(v_e_1109_);
v___x_1324_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__3);
v___x_1325_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7(v___x_1324_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
return v___x_1325_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1107_ = stack[0].m_obj;
lean_object* v___x_1108_ = stack[1].m_obj;
lean_object* v_e_1109_ = stack[2].m_obj;
lean_object* v_offset_1110_ = stack[3].m_obj;
lean_object* v_a_1111_ = stack[4].m_obj;
uint8_t v_a_1112_ = stack[5].m_num;
lean_object* v_a_1113_ = stack[6].m_obj;
lean_object* v_a_1114_ = stack[7].m_obj;
lean_object* v_res_1326_;
v_res_1326_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0(v___x_1107_, v___x_1108_, v_e_1109_, v_offset_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
stack->m_obj
 = v_res_1326_;
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(lean_object* v___x_1327_, lean_object* v___x_1328_, lean_object* v_e_1329_, lean_object* v_offset_1330_, lean_object* v_a_1331_, uint8_t v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_key_1335_; lean_object* v___x_1336_; 
lean_inc(v_offset_1330_);
lean_inc_ref(v_e_1329_);
v_key_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1335_, 0, v_e_1329_);
lean_ctor_set(v_key_1335_, 1, v_offset_1330_);
v___x_1336_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___redArg(v_a_1331_, v_key_1335_);
if (lean_obj_tag(v___x_1336_) == 1)
{
lean_object* v_val_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_dec_ref_known(v_key_1335_, 2);
lean_dec(v_offset_1330_);
lean_dec_ref(v_e_1329_);
v_val_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_val_1337_);
lean_dec_ref_known(v___x_1336_, 1);
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v_val_1337_);
lean_ctor_set(v___x_1338_, 1, v_a_1331_);
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
lean_ctor_set(v___x_1339_, 1, v_a_1334_);
return v___x_1339_;
}
else
{
lean_dec(v___x_1336_);
switch(lean_obj_tag(v_e_1329_))
{
case 0:
{
lean_object* v_deBruijnIndex_1340_; uint8_t v___x_1341_; 
v_deBruijnIndex_1340_ = lean_ctor_get(v_e_1329_, 0);
v___x_1341_ = lean_nat_dec_le(v_offset_1330_, v_deBruijnIndex_1340_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; 
lean_dec(v_offset_1330_);
v___x_1342_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1335_, v_e_1329_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1342_;
}
else
{
lean_object* v_size_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
lean_inc(v_deBruijnIndex_1340_);
lean_dec_ref_known(v_e_1329_, 1);
v_size_1343_ = lean_ctor_get(v___x_1328_, 2);
v___x_1344_ = l_Lean_instInhabitedExpr;
v___x_1345_ = lean_nat_sub(v_deBruijnIndex_1340_, v_offset_1330_);
lean_dec(v_offset_1330_);
lean_dec(v_deBruijnIndex_1340_);
v___x_1346_ = lean_nat_sub(v___x_1327_, v___x_1345_);
lean_dec(v___x_1345_);
v___x_1347_ = lean_unsigned_to_nat(1u);
v___x_1348_ = lean_nat_sub(v___x_1346_, v___x_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_nat_dec_lt(v___x_1348_, v_size_1343_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
lean_dec(v___x_1348_);
v___x_1350_ = l_outOfBounds___redArg(v___x_1344_);
v___x_1351_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1335_, v___x_1350_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1351_;
}
else
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1344_, v___x_1328_, v___x_1348_);
lean_dec(v___x_1348_);
v___x_1353_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1335_, v___x_1352_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1353_;
}
}
}
case 9:
{
lean_object* v___x_1354_; 
lean_dec(v_offset_1330_);
v___x_1354_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1335_, v_e_1329_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1354_;
}
case 2:
{
lean_object* v___x_1355_; 
lean_dec(v_offset_1330_);
v___x_1355_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1335_, v_e_1329_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1355_;
}
case 1:
{
lean_object* v___x_1356_; 
lean_dec(v_offset_1330_);
v___x_1356_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1335_, v_e_1329_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1356_;
}
case 4:
{
lean_object* v___x_1357_; 
lean_dec(v_offset_1330_);
v___x_1357_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1335_, v_e_1329_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1357_;
}
case 3:
{
lean_object* v___x_1358_; 
lean_dec(v_offset_1330_);
v___x_1358_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1335_, v_e_1329_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1358_;
}
default: 
{
lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1359_ = l_Lean_Expr_looseBVarRange(v_e_1329_);
v___x_1360_ = lean_nat_dec_le(v___x_1359_, v_offset_1330_);
lean_dec(v___x_1359_);
if (v___x_1360_ == 0)
{
switch(lean_obj_tag(v_e_1329_))
{
case 9:
{
lean_object* v___x_1361_; 
lean_dec(v_offset_1330_);
v___x_1361_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1335_, v_e_1329_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1361_;
}
case 2:
{
lean_object* v___x_1362_; 
lean_dec(v_offset_1330_);
v___x_1362_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1335_, v_e_1329_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1362_;
}
case 0:
{
lean_object* v___x_1363_; 
lean_dec(v_offset_1330_);
v___x_1363_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1335_, v_e_1329_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1363_;
}
case 1:
{
lean_object* v___x_1364_; 
lean_dec(v_offset_1330_);
v___x_1364_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1335_, v_e_1329_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1364_;
}
case 4:
{
lean_object* v___x_1365_; 
lean_dec(v_offset_1330_);
v___x_1365_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1335_, v_e_1329_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1365_;
}
case 3:
{
lean_object* v___x_1366_; 
lean_dec(v_offset_1330_);
v___x_1366_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1335_, v_e_1329_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1366_;
}
default: 
{
lean_object* v___x_1367_; 
v___x_1367_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0(v___x_1327_, v___x_1328_, v_e_1329_, v_offset_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v_a_1369_; lean_object* v_fst_1370_; lean_object* v_snd_1371_; lean_object* v___x_1372_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
v_a_1369_ = lean_ctor_get(v___x_1367_, 1);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1367_, 2);
v_fst_1370_ = lean_ctor_get(v_a_1368_, 0);
lean_inc(v_fst_1370_);
v_snd_1371_ = lean_ctor_get(v_a_1368_, 1);
lean_inc(v_snd_1371_);
lean_dec(v_a_1368_);
v___x_1372_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1335_, v_fst_1370_, v_snd_1371_, v_a_1332_, v_a_1333_, v_a_1369_);
return v___x_1372_;
}
else
{
lean_dec_ref_known(v_key_1335_, 2);
return v___x_1367_;
}
}
}
}
else
{
lean_object* v___x_1373_; 
lean_dec(v_offset_1330_);
v___x_1373_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1335_, v_e_1329_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1373_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1327_ = stack[0].m_obj;
lean_object* v___x_1328_ = stack[1].m_obj;
lean_object* v_e_1329_ = stack[2].m_obj;
lean_object* v_offset_1330_ = stack[3].m_obj;
lean_object* v_a_1331_ = stack[4].m_obj;
uint8_t v_a_1332_ = stack[5].m_num;
lean_object* v_a_1333_ = stack[6].m_obj;
lean_object* v_a_1334_ = stack[7].m_obj;
lean_object* v_res_1374_;
v_res_1374_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1327_, v___x_1328_, v_e_1329_, v_offset_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
stack->m_obj
 = v_res_1374_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0___boxed(lean_object* v___x_1375_, lean_object* v___x_1376_, lean_object* v_e_1377_, lean_object* v_offset_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
uint8_t v_a_boxed_1383_; lean_object* v_res_1384_; 
v_a_boxed_1383_ = lean_unbox(v_a_1380_);
v_res_1384_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1375_, v___x_1376_, v_e_1377_, v_offset_1378_, v_a_1379_, v_a_boxed_1383_, v_a_1381_, v_a_1382_);
lean_dec_ref(v_a_1381_);
lean_dec_ref(v___x_1376_);
lean_dec(v___x_1375_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___boxed(lean_object* v___x_1385_, lean_object* v___x_1386_, lean_object* v_e_1387_, lean_object* v_offset_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
uint8_t v_a_boxed_1393_; lean_object* v_res_1394_; 
v_a_boxed_1393_ = lean_unbox(v_a_1390_);
v_res_1394_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0(v___x_1385_, v___x_1386_, v_e_1387_, v_offset_1388_, v_a_1389_, v_a_boxed_1393_, v_a_1391_, v_a_1392_);
lean_dec_ref(v_a_1391_);
lean_dec_ref(v___x_1386_);
lean_dec(v___x_1385_);
return v_res_1394_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1395_ = lean_box(0);
v___x_1396_ = lean_unsigned_to_nat(16u);
v___x_1397_ = lean_mk_array(v___x_1396_, v___x_1395_);
return v___x_1397_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1398_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__0, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__0);
v___x_1399_ = lean_unsigned_to_nat(0u);
v___x_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
lean_ctor_set(v___x_1400_, 1, v___x_1398_);
return v___x_1400_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0(lean_object* v_e_1401_, lean_object* v_size_1402_, lean_object* v___x_1403_, lean_object* v_xs_1404_, uint8_t v_debug_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1401_))
{
case 0:
{
lean_object* v_deBruijnIndex_1409_; uint8_t v___x_1410_; 
v_deBruijnIndex_1409_ = lean_ctor_get(v_e_1401_, 0);
v___x_1410_ = lean_nat_dec_le(v___x_1408_, v_deBruijnIndex_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; 
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v_e_1401_);
lean_ctor_set(v___x_1411_, 1, v___y_1407_);
return v___x_1411_;
}
else
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
lean_inc(v_deBruijnIndex_1409_);
lean_dec_ref_known(v_e_1401_, 1);
v___x_1412_ = lean_nat_sub(v_size_1402_, v_deBruijnIndex_1409_);
lean_dec(v_deBruijnIndex_1409_);
v___x_1413_ = lean_unsigned_to_nat(1u);
v___x_1414_ = lean_nat_sub(v___x_1412_, v___x_1413_);
lean_dec(v___x_1412_);
v___x_1415_ = lean_nat_dec_lt(v___x_1414_, v_size_1402_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
lean_dec(v___x_1414_);
v___x_1416_ = l_outOfBounds___redArg(v___x_1403_);
v___x_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
lean_ctor_set(v___x_1417_, 1, v___y_1407_);
return v___x_1417_;
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1403_, v_xs_1404_, v___x_1414_);
lean_dec(v___x_1414_);
v___x_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
lean_ctor_set(v___x_1419_, 1, v___y_1407_);
return v___x_1419_;
}
}
}
case 9:
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1420_, 0, v_e_1401_);
lean_ctor_set(v___x_1420_, 1, v___y_1407_);
return v___x_1420_;
}
case 2:
{
lean_object* v___x_1421_; 
v___x_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1421_, 0, v_e_1401_);
lean_ctor_set(v___x_1421_, 1, v___y_1407_);
return v___x_1421_;
}
case 1:
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1422_, 0, v_e_1401_);
lean_ctor_set(v___x_1422_, 1, v___y_1407_);
return v___x_1422_;
}
case 4:
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1423_, 0, v_e_1401_);
lean_ctor_set(v___x_1423_, 1, v___y_1407_);
return v___x_1423_;
}
case 3:
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v_e_1401_);
lean_ctor_set(v___x_1424_, 1, v___y_1407_);
return v___x_1424_;
}
default: 
{
lean_object* v___x_1425_; uint8_t v___x_1426_; 
v___x_1425_ = l_Lean_Expr_looseBVarRange(v_e_1401_);
v___x_1426_ = lean_nat_dec_le(v___x_1425_, v___x_1408_);
lean_dec(v___x_1425_);
if (v___x_1426_ == 0)
{
switch(lean_obj_tag(v_e_1401_))
{
case 9:
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1427_, 0, v_e_1401_);
lean_ctor_set(v___x_1427_, 1, v___y_1407_);
return v___x_1427_;
}
case 2:
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1428_, 0, v_e_1401_);
lean_ctor_set(v___x_1428_, 1, v___y_1407_);
return v___x_1428_;
}
case 0:
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1429_, 0, v_e_1401_);
lean_ctor_set(v___x_1429_, 1, v___y_1407_);
return v___x_1429_;
}
case 1:
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1430_, 0, v_e_1401_);
lean_ctor_set(v___x_1430_, 1, v___y_1407_);
return v___x_1430_;
}
case 4:
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v_e_1401_);
lean_ctor_set(v___x_1431_, 1, v___y_1407_);
return v___x_1431_;
}
case 3:
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v_e_1401_);
lean_ctor_set(v___x_1432_, 1, v___y_1407_);
return v___x_1432_;
}
default: 
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__1);
v___x_1434_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0(v_size_1402_, v_xs_1404_, v_e_1401_, v___x_1408_, v___x_1433_, v_debug_1405_, v___y_1406_, v___y_1407_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1444_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
v_a_1436_ = lean_ctor_get(v___x_1434_, 1);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1438_ = v___x_1434_;
v_isShared_1439_ = v_isSharedCheck_1444_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_inc(v_a_1435_);
lean_dec(v___x_1434_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1444_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v_fst_1440_; lean_object* v___x_1442_; 
v_fst_1440_ = lean_ctor_get(v_a_1435_, 0);
lean_inc(v_fst_1440_);
lean_dec(v_a_1435_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v_fst_1440_);
v___x_1442_ = v___x_1438_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_fst_1440_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_a_1436_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
v_a_1445_ = lean_ctor_get(v___x_1434_, 0);
v_a_1446_ = lean_ctor_get(v___x_1434_, 1);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1434_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_inc(v_a_1445_);
lean_dec(v___x_1434_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1445_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
}
}
else
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v_e_1401_);
lean_ctor_set(v___x_1454_, 1, v___y_1407_);
return v___x_1454_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1401_ = stack[0].m_obj;
lean_object* v_size_1402_ = stack[1].m_obj;
lean_object* v___x_1403_ = stack[2].m_obj;
lean_object* v_xs_1404_ = stack[3].m_obj;
uint8_t v_debug_1405_ = stack[4].m_num;
lean_object* v___y_1406_ = stack[5].m_obj;
lean_object* v___y_1407_ = stack[6].m_obj;
lean_object* v_res_1455_;
v_res_1455_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0(v_e_1401_, v_size_1402_, v___x_1403_, v_xs_1404_, v_debug_1405_, v___y_1406_, v___y_1407_);
stack->m_obj
 = v_res_1455_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___boxed(lean_object* v_e_1456_, lean_object* v_size_1457_, lean_object* v___x_1458_, lean_object* v_xs_1459_, lean_object* v_debug_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
uint8_t v_debug_boxed_1463_; lean_object* v_res_1464_; 
v_debug_boxed_1463_ = lean_unbox(v_debug_1460_);
v_res_1464_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0(v_e_1456_, v_size_1457_, v___x_1458_, v_xs_1459_, v_debug_boxed_1463_, v___y_1461_, v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec_ref(v_xs_1459_);
lean_dec_ref(v___x_1458_);
lean_dec(v_size_1457_);
return v_res_1464_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__2(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1467_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_1468_ = lean_unsigned_to_nat(16u);
v___x_1469_ = lean_unsigned_to_nat(62u);
v___x_1470_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__1));
v___x_1471_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__0));
v___x_1472_ = l_mkPanicMessageWithDecl(v___x_1471_, v___x_1470_, v___x_1469_, v___x_1468_, v___x_1467_);
return v___x_1472_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(lean_object* v_e_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v_a_1484_; uint8_t v___x_1502_; 
v___x_1502_ = l_Lean_Expr_hasLooseBVars(v_e_1473_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1503_, 0, v_e_1473_);
return v___x_1503_;
}
else
{
lean_object* v___x_1504_; uint8_t v___x_1505_; lean_object* v___x_1506_; lean_object* v_subst_1507_; lean_object* v___x_1508_; 
v___x_1504_ = l_Lean_instInhabitedExpr;
v___x_1505_ = 0;
v___x_1506_ = lean_st_ref_get(v_a_1475_);
v_subst_1507_ = lean_ctor_get(v___x_1506_, 2);
lean_inc_ref(v_subst_1507_);
lean_dec(v___x_1506_);
v___x_1508_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_subst_1507_, v_e_1473_);
lean_dec_ref(v_subst_1507_);
if (lean_obj_tag(v___x_1508_) == 1)
{
lean_object* v_val_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_dec_ref(v_e_1473_);
v_val_1509_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1508_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_val_1509_);
lean_dec(v___x_1508_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set_tag(v___x_1511_, 0);
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_val_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
else
{
lean_object* v_xs_1517_; lean_object* v_size_1518_; lean_object* v___x_1519_; uint8_t v_debug_1520_; lean_object* v___x_1521_; lean_object* v___f_1522_; lean_object* v___x_1523_; lean_object* v_env_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_dec(v___x_1508_);
v_xs_1517_ = lean_ctor_get(v_a_1474_, 0);
v_size_1518_ = lean_ctor_get(v_xs_1517_, 2);
v___x_1519_ = lean_st_ref_get(v_a_1477_);
v_debug_1520_ = lean_ctor_get_uint8(v___x_1519_, sizeof(void*)*12);
lean_dec(v___x_1519_);
v___x_1521_ = lean_box(v_debug_1520_);
lean_inc_ref(v_xs_1517_);
lean_inc(v_size_1518_);
lean_inc_ref(v_e_1473_);
v___f_1522_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___boxed), 7, 5);
lean_closure_set(v___f_1522_, 0, v_e_1473_);
lean_closure_set(v___f_1522_, 1, v_size_1518_);
lean_closure_set(v___f_1522_, 2, v___x_1504_);
lean_closure_set(v___f_1522_, 3, v_xs_1517_);
lean_closure_set(v___f_1522_, 4, v___x_1521_);
v___x_1523_ = lean_st_ref_get(v_a_1481_);
v_env_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc_ref(v_env_1524_);
lean_dec(v___x_1523_);
v___x_1525_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1525_, 0, v_env_1524_);
lean_ctor_set_uint8(v___x_1525_, sizeof(void*)*1, v___x_1505_);
lean_ctor_set_uint8(v___x_1525_, sizeof(void*)*1 + 1, v___x_1505_);
v___x_1526_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1522_, v___x_1525_, v_a_1477_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1526_, 1);
if (lean_obj_tag(v_a_1527_) == 0)
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec_ref_known(v_a_1527_, 1);
v___x_1528_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__2, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__2_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__2);
v___x_1529_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1(v___x_1528_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
v_a_1484_ = v_a_1530_;
goto v___jp_1483_;
}
else
{
lean_dec_ref(v_e_1473_);
return v___x_1529_;
}
}
else
{
lean_object* v_a_1531_; 
v_a_1531_ = lean_ctor_get(v_a_1527_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v_a_1527_, 1);
v_a_1484_ = v_a_1531_;
goto v___jp_1483_;
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec_ref(v_e_1473_);
v_a_1532_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1526_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1526_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
}
v___jp_1483_:
{
lean_object* v___x_1485_; lean_object* v_visited_1486_; lean_object* v_types_1487_; lean_object* v_subst_1488_; lean_object* v_visitedClosed_1489_; lean_object* v_hasDepLetCache_1490_; lean_object* v_numConverted_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1501_; 
v___x_1485_ = lean_st_ref_take(v_a_1475_);
v_visited_1486_ = lean_ctor_get(v___x_1485_, 0);
v_types_1487_ = lean_ctor_get(v___x_1485_, 1);
v_subst_1488_ = lean_ctor_get(v___x_1485_, 2);
v_visitedClosed_1489_ = lean_ctor_get(v___x_1485_, 3);
v_hasDepLetCache_1490_ = lean_ctor_get(v___x_1485_, 4);
v_numConverted_1491_ = lean_ctor_get(v___x_1485_, 5);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1493_ = v___x_1485_;
v_isShared_1494_ = v_isSharedCheck_1501_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_numConverted_1491_);
lean_inc(v_hasDepLetCache_1490_);
lean_inc(v_visitedClosed_1489_);
lean_inc(v_subst_1488_);
lean_inc(v_types_1487_);
lean_inc(v_visited_1486_);
lean_dec(v___x_1485_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1501_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
lean_inc_ref(v_a_1484_);
v___x_1495_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_subst_1488_, v_e_1473_, v_a_1484_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 2, v___x_1495_);
v___x_1497_ = v___x_1493_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_visited_1486_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_types_1487_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_visitedClosed_1489_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_hasDepLetCache_1490_);
lean_ctor_set(v_reuseFailAlloc_1500_, 5, v_numConverted_1491_);
v___x_1497_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = lean_st_ref_put(v_a_1475_, v___x_1497_);
v___x_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1499_, 0, v_a_1484_);
return v___x_1499_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1473_ = stack[0].m_obj;
lean_object* v_a_1474_ = stack[1].m_obj;
lean_object* v_a_1475_ = stack[2].m_obj;
lean_object* v_a_1476_ = stack[3].m_obj;
lean_object* v_a_1477_ = stack[4].m_obj;
lean_object* v_a_1478_ = stack[5].m_obj;
lean_object* v_a_1479_ = stack[6].m_obj;
lean_object* v_a_1480_ = stack[7].m_obj;
lean_object* v_a_1481_ = stack[8].m_obj;
lean_object* v_res_1540_;
v_res_1540_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_e_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_);
stack->m_obj
 = v_res_1540_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___boxed(lean_object* v_e_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_e_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
lean_dec(v_a_1549_);
lean_dec_ref(v_a_1548_);
lean_dec(v_a_1547_);
lean_dec_ref(v_a_1546_);
lean_dec(v_a_1545_);
lean_dec_ref(v_a_1544_);
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1552_, lean_object* v_m_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___redArg(v_m_1553_, v_a_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1556_, lean_object* v_m_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2(v_00_u03b2_1556_, v_m_1557_, v_a_1558_);
lean_dec_ref(v_a_1558_);
lean_dec_ref(v_m_1557_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_1560_, lean_object* v_a_1561_, lean_object* v_x_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_1561_, v_x_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_1564_, lean_object* v_a_1565_, lean_object* v_x_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10(v_00_u03b2_1564_, v_a_1565_, v_x_1566_);
lean_dec(v_x_1566_);
lean_dec_ref(v_a_1565_);
return v_res_1567_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(lean_object* v_msgData_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v___x_1574_; lean_object* v_env_1575_; uint8_t v___x_1576_; lean_object* v_env_1577_; lean_object* v___x_1578_; lean_object* v_toCold_1579_; lean_object* v_mctx_1580_; lean_object* v_lctx_1581_; lean_object* v_options_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1574_ = lean_st_ref_get(v___y_1572_);
v_env_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc_ref(v_env_1575_);
lean_dec(v___x_1574_);
v___x_1576_ = 0;
v_env_1577_ = l_Lean_Environment_setRecordingDeps(v_env_1575_, v___x_1576_);
v___x_1578_ = lean_st_ref_get(v___y_1570_);
v_toCold_1579_ = lean_ctor_get(v___y_1571_, 0);
v_mctx_1580_ = lean_ctor_get(v___x_1578_, 0);
lean_inc_ref(v_mctx_1580_);
lean_dec(v___x_1578_);
v_lctx_1581_ = lean_ctor_get(v___y_1569_, 2);
v_options_1582_ = lean_ctor_get(v_toCold_1579_, 2);
lean_inc_ref(v_options_1582_);
lean_inc_ref(v_lctx_1581_);
v___x_1583_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1583_, 0, v_env_1577_);
lean_ctor_set(v___x_1583_, 1, v_mctx_1580_);
lean_ctor_set(v___x_1583_, 2, v_lctx_1581_);
lean_ctor_set(v___x_1583_, 3, v_options_1582_);
v___x_1584_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
lean_ctor_set(v___x_1584_, 1, v_msgData_1568_);
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1568_ = stack[0].m_obj;
lean_object* v___y_1569_ = stack[1].m_obj;
lean_object* v___y_1570_ = stack[2].m_obj;
lean_object* v___y_1571_ = stack[3].m_obj;
lean_object* v___y_1572_ = stack[4].m_obj;
lean_object* v_res_1586_;
v_res_1586_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(v_msgData_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
stack->m_obj
 = v_res_1586_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0___boxed(lean_object* v_msgData_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(v_msgData_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
return v_res_1593_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(lean_object* v_msg_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_ref_1600_; lean_object* v___x_1601_; lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1610_; 
v_ref_1600_ = lean_ctor_get(v___y_1597_, 2);
v___x_1601_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(v_msg_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1610_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1610_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1608_; 
lean_inc(v_ref_1600_);
v___x_1606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1606_, 0, v_ref_1600_);
lean_ctor_set(v___x_1606_, 1, v_a_1602_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set_tag(v___x_1604_, 1);
lean_ctor_set(v___x_1604_, 0, v___x_1606_);
v___x_1608_ = v___x_1604_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1594_ = stack[0].m_obj;
lean_object* v___y_1595_ = stack[1].m_obj;
lean_object* v___y_1596_ = stack[2].m_obj;
lean_object* v___y_1597_ = stack[3].m_obj;
lean_object* v___y_1598_ = stack[4].m_obj;
lean_object* v_res_1611_;
v_res_1611_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v_msg_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
stack->m_obj
 = v_res_1611_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg___boxed(lean_object* v_msg_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v_msg_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
return v_res_1618_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1(void){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__0));
v___x_1621_ = l_Lean_stringToMessageData(v___x_1620_);
return v___x_1621_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3(void){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__2));
v___x_1624_ = l_Lean_stringToMessageData(v___x_1623_);
return v___x_1624_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(lean_object* v_t_1625_, lean_object* v_s_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_){
_start:
{
size_t v___x_1636_; size_t v___x_1637_; uint8_t v___x_1638_; 
v___x_1636_ = lean_ptr_addr(v_t_1625_);
v___x_1637_ = lean_ptr_addr(v_s_1626_);
v___x_1638_ = lean_usize_dec_eq(v___x_1636_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; 
lean_inc_ref(v_s_1626_);
lean_inc_ref(v_t_1625_);
v___x_1639_ = l_Lean_Meta_isExprDefEq(v_t_1625_, v_s_1626_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1657_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1657_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1657_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
uint8_t v___x_1644_; 
v___x_1644_ = lean_unbox(v_a_1640_);
lean_dec(v_a_1640_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_del_object(v___x_1642_);
v___x_1645_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1);
v___x_1646_ = l_Lean_indentExpr(v_t_1625_);
v___x_1647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1645_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = l_Lean_indentExpr(v_s_1626_);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v___x_1651_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
return v___x_1652_;
}
else
{
lean_object* v___x_1653_; lean_object* v___x_1655_; 
lean_dec_ref(v_s_1626_);
lean_dec_ref(v_t_1625_);
v___x_1653_ = lean_box(0);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1653_);
v___x_1655_ = v___x_1642_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec_ref(v_s_1626_);
lean_dec_ref(v_t_1625_);
v_a_1658_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1639_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1639_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_dec_ref(v_s_1626_);
lean_dec_ref(v_t_1625_);
v___x_1666_ = lean_box(0);
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
return v___x_1667_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1625_ = stack[0].m_obj;
lean_object* v_s_1626_ = stack[1].m_obj;
lean_object* v_a_1627_ = stack[2].m_obj;
lean_object* v_a_1628_ = stack[3].m_obj;
lean_object* v_a_1629_ = stack[4].m_obj;
lean_object* v_a_1630_ = stack[5].m_obj;
lean_object* v_a_1631_ = stack[6].m_obj;
lean_object* v_a_1632_ = stack[7].m_obj;
lean_object* v_a_1633_ = stack[8].m_obj;
lean_object* v_a_1634_ = stack[9].m_obj;
lean_object* v_res_1668_;
v_res_1668_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_t_1625_, v_s_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
stack->m_obj
 = v_res_1668_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___boxed(lean_object* v_t_1669_, lean_object* v_s_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_t_1669_, v_s_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
return v_res_1680_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0(lean_object* v_00_u03b1_1681_, lean_object* v_msg_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v_msg_1682_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1682_ = stack[1].m_obj;
lean_object* v___y_1683_ = stack[2].m_obj;
lean_object* v___y_1684_ = stack[3].m_obj;
lean_object* v___y_1685_ = stack[4].m_obj;
lean_object* v___y_1686_ = stack[5].m_obj;
lean_object* v___y_1687_ = stack[6].m_obj;
lean_object* v___y_1688_ = stack[7].m_obj;
lean_object* v___y_1689_ = stack[8].m_obj;
lean_object* v___y_1690_ = stack[9].m_obj;
lean_object* v_res_1693_;
v_res_1693_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0(lean_box(0), v_msg_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
stack->m_obj
 = v_res_1693_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___boxed(lean_object* v_00_u03b1_1694_, lean_object* v_msg_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0(v_00_u03b1_1694_, v_msg_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
return v_res_1705_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1(void){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__0));
v___x_1708_ = l_Lean_stringToMessageData(v___x_1707_);
return v___x_1708_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(lean_object* v_type_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
uint8_t v___x_1717_; 
v___x_1717_ = l_Lean_Expr_isForall(v_type_1709_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; 
lean_inc(v_a_1715_);
lean_inc_ref(v_a_1714_);
lean_inc(v_a_1713_);
lean_inc_ref(v_a_1712_);
v___x_1718_ = lean_whnf(v_type_1709_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; uint8_t v___x_1720_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
v___x_1720_ = l_Lean_Expr_isForall(v_a_1719_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
v___x_1721_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1);
v___x_1722_ = l_Lean_indentExpr(v_a_1719_);
v___x_1723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1721_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
v___x_1724_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v___x_1723_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_);
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
else
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_Meta_Sym_shareCommon(v_a_1719_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_);
return v___x_1733_;
}
}
else
{
return v___x_1718_;
}
}
else
{
lean_object* v___x_1734_; 
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v_type_1709_);
return v___x_1734_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1709_ = stack[0].m_obj;
lean_object* v_a_1710_ = stack[1].m_obj;
lean_object* v_a_1711_ = stack[2].m_obj;
lean_object* v_a_1712_ = stack[3].m_obj;
lean_object* v_a_1713_ = stack[4].m_obj;
lean_object* v_a_1714_ = stack[5].m_obj;
lean_object* v_a_1715_ = stack[6].m_obj;
lean_object* v_res_1735_;
v_res_1735_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_type_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_);
stack->m_obj
 = v_res_1735_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___boxed(lean_object* v_type_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_type_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
return v_res_1744_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall(lean_object* v_type_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_type_1745_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
return v___x_1755_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1745_ = stack[0].m_obj;
lean_object* v_a_1746_ = stack[1].m_obj;
lean_object* v_a_1747_ = stack[2].m_obj;
lean_object* v_a_1748_ = stack[3].m_obj;
lean_object* v_a_1749_ = stack[4].m_obj;
lean_object* v_a_1750_ = stack[5].m_obj;
lean_object* v_a_1751_ = stack[6].m_obj;
lean_object* v_a_1752_ = stack[7].m_obj;
lean_object* v_a_1753_ = stack[8].m_obj;
lean_object* v_res_1756_;
v_res_1756_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall(v_type_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
stack->m_obj
 = v_res_1756_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___boxed(lean_object* v_type_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall(v_type_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_);
lean_dec(v_a_1765_);
lean_dec_ref(v_a_1764_);
lean_dec(v_a_1763_);
lean_dec_ref(v_a_1762_);
lean_dec(v_a_1761_);
lean_dec_ref(v_a_1760_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
return v_res_1767_;
}
}
uint8_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_isClean(lean_object* v_e_1768_, lean_object* v_ctx_1769_){
_start:
{
lean_object* v_cleanSuffix_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; 
v_cleanSuffix_1770_ = lean_ctor_get(v_ctx_1769_, 2);
v___x_1771_ = l_Lean_Expr_looseBVarRange(v_e_1768_);
v___x_1772_ = lean_nat_dec_le(v___x_1771_, v_cleanSuffix_1770_);
lean_dec(v___x_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_isClean_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1768_ = stack[0].m_obj;
lean_object* v_ctx_1769_ = stack[1].m_obj;
uint8_t v_res_1773_;
v_res_1773_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_isClean(v_e_1768_, v_ctx_1769_);
stack->m_num = v_res_1773_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_isClean___boxed(lean_object* v_e_1774_, lean_object* v_ctx_1775_){
_start:
{
uint8_t v_res_1776_; lean_object* v_r_1777_; 
v_res_1776_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_isClean(v_e_1774_, v_ctx_1775_);
lean_dec_ref(v_ctx_1775_);
lean_dec_ref(v_e_1774_);
v_r_1777_ = lean_box(v_res_1776_);
return v_r_1777_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(lean_object* v_e_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_e_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v_keyedConfig_1790_; uint8_t v_trackZetaDelta_1791_; lean_object* v_zetaDeltaSet_1792_; lean_object* v_lctx_1793_; lean_object* v_localInstances_1794_; lean_object* v_defEqCtx_x3f_1795_; lean_object* v_synthPendingDepth_1796_; lean_object* v_customCanUnfoldPredicate_x3f_1797_; uint8_t v_univApprox_1798_; uint8_t v_inTypeClassResolution_1799_; uint8_t v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
v_keyedConfig_1790_ = lean_ctor_get(v_a_1783_, 0);
v_trackZetaDelta_1791_ = lean_ctor_get_uint8(v_a_1783_, sizeof(void*)*7);
v_zetaDeltaSet_1792_ = lean_ctor_get(v_a_1783_, 1);
v_lctx_1793_ = lean_ctor_get(v_a_1783_, 2);
v_localInstances_1794_ = lean_ctor_get(v_a_1783_, 3);
v_defEqCtx_x3f_1795_ = lean_ctor_get(v_a_1783_, 4);
v_synthPendingDepth_1796_ = lean_ctor_get(v_a_1783_, 5);
v_customCanUnfoldPredicate_x3f_1797_ = lean_ctor_get(v_a_1783_, 6);
v_univApprox_1798_ = lean_ctor_get_uint8(v_a_1783_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1799_ = lean_ctor_get_uint8(v_a_1783_, sizeof(void*)*7 + 2);
v___x_1800_ = 0;
lean_inc(v_customCanUnfoldPredicate_x3f_1797_);
lean_inc(v_synthPendingDepth_1796_);
lean_inc(v_defEqCtx_x3f_1795_);
lean_inc_ref(v_localInstances_1794_);
lean_inc_ref(v_lctx_1793_);
lean_inc(v_zetaDeltaSet_1792_);
lean_inc_ref(v_keyedConfig_1790_);
v___x_1801_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1801_, 0, v_keyedConfig_1790_);
lean_ctor_set(v___x_1801_, 1, v_zetaDeltaSet_1792_);
lean_ctor_set(v___x_1801_, 2, v_lctx_1793_);
lean_ctor_set(v___x_1801_, 3, v_localInstances_1794_);
lean_ctor_set(v___x_1801_, 4, v_defEqCtx_x3f_1795_);
lean_ctor_set(v___x_1801_, 5, v_synthPendingDepth_1796_);
lean_ctor_set(v___x_1801_, 6, v_customCanUnfoldPredicate_x3f_1797_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*7, v_trackZetaDelta_1791_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*7 + 1, v_univApprox_1798_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1799_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*7 + 3, v___x_1800_);
lean_inc(v_a_1786_);
lean_inc_ref(v_a_1785_);
lean_inc(v_a_1784_);
v___x_1802_ = lean_infer_type(v_a_1789_, v___x_1801_, v_a_1784_, v_a_1785_, v_a_1786_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1804_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref_known(v___x_1802_, 1);
v___x_1804_ = l_Lean_Meta_Sym_shareCommon(v_a_1803_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
return v___x_1804_;
}
else
{
return v___x_1802_;
}
}
else
{
return v___x_1788_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1778_ = stack[0].m_obj;
lean_object* v_a_1779_ = stack[1].m_obj;
lean_object* v_a_1780_ = stack[2].m_obj;
lean_object* v_a_1781_ = stack[3].m_obj;
lean_object* v_a_1782_ = stack[4].m_obj;
lean_object* v_a_1783_ = stack[5].m_obj;
lean_object* v_a_1784_ = stack[6].m_obj;
lean_object* v_a_1785_ = stack[7].m_obj;
lean_object* v_a_1786_ = stack[8].m_obj;
lean_object* v_res_1805_;
v_res_1805_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(v_e_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
stack->m_obj
 = v_res_1805_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback___boxed(lean_object* v_e_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(v_e_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
lean_dec(v_a_1808_);
lean_dec_ref(v_a_1807_);
return v_res_1816_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_instMonadEIO___redArg();
return v___x_1817_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(lean_object* v_msg_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v_toApplicative_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1899_; 
v___x_1832_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0);
v___x_1833_ = l_StateRefT_x27_instMonad___redArg(v___x_1832_);
v_toApplicative_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; 
v_unused_1900_ = lean_ctor_get(v___x_1833_, 1);
lean_dec(v_unused_1900_);
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1899_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_toApplicative_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1899_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v_toFunctor_1838_; lean_object* v_toSeq_1839_; lean_object* v_toSeqLeft_1840_; lean_object* v_toSeqRight_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1897_; 
v_toFunctor_1838_ = lean_ctor_get(v_toApplicative_1834_, 0);
v_toSeq_1839_ = lean_ctor_get(v_toApplicative_1834_, 2);
v_toSeqLeft_1840_ = lean_ctor_get(v_toApplicative_1834_, 3);
v_toSeqRight_1841_ = lean_ctor_get(v_toApplicative_1834_, 4);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_toApplicative_1834_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; 
v_unused_1898_ = lean_ctor_get(v_toApplicative_1834_, 1);
lean_dec(v_unused_1898_);
v___x_1843_ = v_toApplicative_1834_;
v_isShared_1844_ = v_isSharedCheck_1897_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_toSeqRight_1841_);
lean_inc(v_toSeqLeft_1840_);
lean_inc(v_toSeq_1839_);
lean_inc(v_toFunctor_1838_);
lean_dec(v_toApplicative_1834_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1897_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___f_1845_; lean_object* v___f_1846_; lean_object* v___f_1847_; lean_object* v___f_1848_; lean_object* v___x_1849_; lean_object* v___f_1850_; lean_object* v___f_1851_; lean_object* v___f_1852_; lean_object* v___x_1854_; 
v___f_1845_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__1));
v___f_1846_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1838_);
v___f_1847_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1847_, 0, v_toFunctor_1838_);
v___f_1848_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1848_, 0, v_toFunctor_1838_);
v___x_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___f_1847_);
lean_ctor_set(v___x_1849_, 1, v___f_1848_);
v___f_1850_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1850_, 0, v_toSeqRight_1841_);
v___f_1851_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1851_, 0, v_toSeqLeft_1840_);
v___f_1852_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1852_, 0, v_toSeq_1839_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 4, v___f_1850_);
lean_ctor_set(v___x_1843_, 3, v___f_1851_);
lean_ctor_set(v___x_1843_, 2, v___f_1852_);
lean_ctor_set(v___x_1843_, 1, v___f_1845_);
lean_ctor_set(v___x_1843_, 0, v___x_1849_);
v___x_1854_ = v___x_1843_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1849_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v___f_1845_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v___f_1852_);
lean_ctor_set(v_reuseFailAlloc_1896_, 3, v___f_1851_);
lean_ctor_set(v_reuseFailAlloc_1896_, 4, v___f_1850_);
v___x_1854_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1856_; 
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 1, v___f_1846_);
lean_ctor_set(v___x_1836_, 0, v___x_1854_);
v___x_1856_ = v___x_1836_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v___f_1846_);
v___x_1856_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; lean_object* v_toApplicative_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1893_; 
v___x_1857_ = l_StateRefT_x27_instMonad___redArg(v___x_1856_);
v_toApplicative_1858_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; 
v_unused_1894_ = lean_ctor_get(v___x_1857_, 1);
lean_dec(v_unused_1894_);
v___x_1860_ = v___x_1857_;
v_isShared_1861_ = v_isSharedCheck_1893_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_toApplicative_1858_);
lean_dec(v___x_1857_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1893_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v_toFunctor_1862_; lean_object* v_toSeq_1863_; lean_object* v_toSeqLeft_1864_; lean_object* v_toSeqRight_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1891_; 
v_toFunctor_1862_ = lean_ctor_get(v_toApplicative_1858_, 0);
v_toSeq_1863_ = lean_ctor_get(v_toApplicative_1858_, 2);
v_toSeqLeft_1864_ = lean_ctor_get(v_toApplicative_1858_, 3);
v_toSeqRight_1865_ = lean_ctor_get(v_toApplicative_1858_, 4);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_toApplicative_1858_);
if (v_isSharedCheck_1891_ == 0)
{
lean_object* v_unused_1892_; 
v_unused_1892_ = lean_ctor_get(v_toApplicative_1858_, 1);
lean_dec(v_unused_1892_);
v___x_1867_ = v_toApplicative_1858_;
v_isShared_1868_ = v_isSharedCheck_1891_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_toSeqRight_1865_);
lean_inc(v_toSeqLeft_1864_);
lean_inc(v_toSeq_1863_);
lean_inc(v_toFunctor_1862_);
lean_dec(v_toApplicative_1858_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1891_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___f_1869_; lean_object* v___f_1870_; lean_object* v___f_1871_; lean_object* v___f_1872_; lean_object* v___x_1873_; lean_object* v___f_1874_; lean_object* v___f_1875_; lean_object* v___f_1876_; lean_object* v___x_1878_; 
v___f_1869_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__3));
v___f_1870_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1862_);
v___f_1871_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1871_, 0, v_toFunctor_1862_);
v___f_1872_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1872_, 0, v_toFunctor_1862_);
v___x_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___f_1871_);
lean_ctor_set(v___x_1873_, 1, v___f_1872_);
v___f_1874_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1874_, 0, v_toSeqRight_1865_);
v___f_1875_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1875_, 0, v_toSeqLeft_1864_);
v___f_1876_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1876_, 0, v_toSeq_1863_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 4, v___f_1874_);
lean_ctor_set(v___x_1867_, 3, v___f_1875_);
lean_ctor_set(v___x_1867_, 2, v___f_1876_);
lean_ctor_set(v___x_1867_, 1, v___f_1869_);
lean_ctor_set(v___x_1867_, 0, v___x_1873_);
v___x_1878_ = v___x_1867_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1873_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v___f_1869_);
lean_ctor_set(v_reuseFailAlloc_1890_, 2, v___f_1876_);
lean_ctor_set(v_reuseFailAlloc_1890_, 3, v___f_1875_);
lean_ctor_set(v_reuseFailAlloc_1890_, 4, v___f_1874_);
v___x_1878_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1880_; 
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 1, v___f_1870_);
lean_ctor_set(v___x_1860_, 0, v___x_1878_);
v___x_1880_ = v___x_1860_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v___f_1870_);
v___x_1880_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___f_1886_; lean_object* v___x_11696__overap_1887_; lean_object* v___x_1888_; 
v___x_1881_ = l_StateRefT_x27_instMonad___redArg(v___x_1880_);
v___x_1882_ = l_ReaderT_instMonad___redArg(v___x_1881_);
v___x_1883_ = l_StateRefT_x27_instMonad___redArg(v___x_1882_);
v___x_1884_ = l_Lean_instInhabitedExpr;
v___x_1885_ = l_instInhabitedOfMonad___redArg(v___x_1883_, v___x_1884_);
v___f_1886_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1886_, 0, v___x_1885_);
v___x_11696__overap_1887_ = lean_panic_fn_borrowed(v___f_1886_, v_msg_1822_);
lean_dec_ref(v___f_1886_);
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
lean_inc(v___y_1828_);
lean_inc_ref(v___y_1827_);
lean_inc(v___y_1826_);
lean_inc_ref(v___y_1825_);
lean_inc(v___y_1824_);
lean_inc_ref(v___y_1823_);
v___x_1888_ = lean_apply_9(v___x_11696__overap_1887_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, lean_box(0));
return v___x_1888_;
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
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1822_ = stack[0].m_obj;
lean_object* v___y_1823_ = stack[1].m_obj;
lean_object* v___y_1824_ = stack[2].m_obj;
lean_object* v___y_1825_ = stack[3].m_obj;
lean_object* v___y_1826_ = stack[4].m_obj;
lean_object* v___y_1827_ = stack[5].m_obj;
lean_object* v___y_1828_ = stack[6].m_obj;
lean_object* v___y_1829_ = stack[7].m_obj;
lean_object* v___y_1830_ = stack[8].m_obj;
lean_object* v_res_1901_;
v_res_1901_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(v_msg_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
stack->m_obj
 = v_res_1901_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___boxed(lean_object* v_msg_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(v_msg_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
return v_res_1912_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2(void){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1915_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_1916_ = lean_unsigned_to_nat(44u);
v___x_1917_ = lean_unsigned_to_nat(367u);
v___x_1918_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__1));
v___x_1919_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0));
v___x_1920_ = l_mkPanicMessageWithDecl(v___x_1919_, v___x_1918_, v___x_1917_, v___x_1916_, v___x_1915_);
return v___x_1920_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(lean_object* v_e_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_){
_start:
{
lean_object* v_type_1932_; lean_object* v___y_1933_; uint8_t v___x_1951_; 
v___x_1951_ = l_Lean_Expr_hasLooseBVars(v_e_1921_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Lean_Meta_Sym_inferType(v_e_1921_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
return v___x_1952_;
}
else
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___y_1956_; lean_object* v_types_1960_; lean_object* v___x_1961_; 
v___x_1953_ = l_Lean_instInhabitedExpr;
v___x_1954_ = lean_st_ref_get(v_a_1923_);
v_types_1960_ = lean_ctor_get(v___x_1954_, 1);
lean_inc_ref(v_types_1960_);
lean_dec(v___x_1954_);
v___x_1961_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_types_1960_, v_e_1921_);
lean_dec_ref(v_types_1960_);
if (lean_obj_tag(v___x_1961_) == 1)
{
lean_object* v_val_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec_ref(v_e_1921_);
v_val_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_val_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
lean_ctor_set_tag(v___x_1964_, 0);
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_val_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
else
{
lean_dec(v___x_1961_);
switch(lean_obj_tag(v_e_1921_))
{
case 0:
{
lean_object* v_xs_1970_; lean_object* v_deBruijnIndex_1971_; lean_object* v_size_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
v_xs_1970_ = lean_ctor_get(v_a_1922_, 0);
v_deBruijnIndex_1971_ = lean_ctor_get(v_e_1921_, 0);
v_size_1972_ = lean_ctor_get(v_xs_1970_, 2);
v___x_1973_ = lean_nat_sub(v_size_1972_, v_deBruijnIndex_1971_);
v___x_1974_ = lean_unsigned_to_nat(1u);
v___x_1975_ = lean_nat_sub(v___x_1973_, v___x_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_nat_dec_lt(v___x_1975_, v_size_1972_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; 
lean_dec(v___x_1975_);
v___x_1977_ = l_outOfBounds___redArg(v___x_1953_);
v___y_1956_ = v___x_1977_;
goto v___jp_1955_;
}
else
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1953_, v_xs_1970_, v___x_1975_);
lean_dec(v___x_1975_);
v___y_1956_ = v___x_1978_;
goto v___jp_1955_;
}
}
case 10:
{
lean_object* v_expr_1979_; lean_object* v___x_1980_; 
v_expr_1979_ = lean_ctor_get(v_e_1921_, 1);
lean_inc_ref(v_expr_1979_);
v___x_1980_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_expr_1979_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref_known(v___x_1980_, 1);
v_type_1932_ = v_a_1981_;
v___y_1933_ = v_a_1923_;
goto v___jp_1931_;
}
else
{
lean_dec_ref_known(v_e_1921_, 2);
return v___x_1980_;
}
}
case 5:
{
lean_object* v_fn_1982_; lean_object* v_arg_1983_; lean_object* v___x_1984_; 
v_fn_1982_ = lean_ctor_get(v_e_1921_, 0);
v_arg_1983_ = lean_ctor_get(v_e_1921_, 1);
lean_inc_ref(v_fn_1982_);
v___x_1984_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_fn_1982_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v___x_1986_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1984_, 1);
v___x_1986_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_a_1985_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1986_, 1);
if (lean_obj_tag(v_a_1987_) == 7)
{
lean_object* v_body_1988_; uint8_t v___x_1989_; 
v_body_1988_ = lean_ctor_get(v_a_1987_, 2);
lean_inc_ref(v_body_1988_);
lean_dec_ref_known(v_a_1987_, 3);
v___x_1989_ = l_Lean_Expr_hasLooseBVars(v_body_1988_);
if (v___x_1989_ == 0)
{
v_type_1932_ = v_body_1988_;
v___y_1933_ = v_a_1923_;
goto v___jp_1931_;
}
else
{
lean_object* v___x_1990_; 
lean_inc_ref(v_arg_1983_);
v___x_1990_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_arg_1983_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1990_, 1);
v___x_1992_ = lean_expr_instantiate1(v_body_1988_, v_a_1991_);
lean_dec(v_a_1991_);
lean_dec_ref(v_body_1988_);
v___x_1993_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1992_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1993_, 1);
v_type_1932_ = v_a_1994_;
v___y_1933_ = v_a_1923_;
goto v___jp_1931_;
}
else
{
lean_dec_ref_known(v_e_1921_, 2);
return v___x_1993_;
}
}
else
{
lean_dec_ref(v_body_1988_);
lean_dec_ref_known(v_e_1921_, 2);
return v___x_1990_;
}
}
}
else
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_dec(v_a_1987_);
v___x_1995_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2);
v___x_1996_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(v___x_1995_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___x_1996_, 1);
v_type_1932_ = v_a_1997_;
v___y_1933_ = v_a_1923_;
goto v___jp_1931_;
}
else
{
lean_dec_ref_known(v_e_1921_, 2);
return v___x_1996_;
}
}
}
else
{
lean_dec_ref_known(v_e_1921_, 2);
return v___x_1986_;
}
}
else
{
lean_dec_ref_known(v_e_1921_, 2);
return v___x_1984_;
}
}
default: 
{
lean_object* v___x_1998_; 
lean_inc_ref(v_e_1921_);
v___x_1998_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(v_e_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
v_type_1932_ = v_a_1999_;
v___y_1933_ = v_a_1923_;
goto v___jp_1931_;
}
else
{
lean_dec_ref(v_e_1921_);
return v___x_1998_;
}
}
}
}
v___jp_1955_:
{
lean_object* v_lctx_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v_lctx_1957_ = lean_ctor_get(v_a_1926_, 2);
lean_inc_ref(v_lctx_1957_);
v___x_1958_ = l_Lean_LocalContext_getFVar_x21(v_lctx_1957_, v___y_1956_);
lean_dec_ref(v___y_1956_);
v___x_1959_ = l_Lean_LocalDecl_type(v___x_1958_);
lean_dec_ref(v___x_1958_);
v_type_1932_ = v___x_1959_;
v___y_1933_ = v_a_1923_;
goto v___jp_1931_;
}
}
v___jp_1931_:
{
lean_object* v___x_1934_; lean_object* v_visited_1935_; lean_object* v_types_1936_; lean_object* v_subst_1937_; lean_object* v_visitedClosed_1938_; lean_object* v_hasDepLetCache_1939_; lean_object* v_numConverted_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1950_; 
v___x_1934_ = lean_st_ref_take(v___y_1933_);
v_visited_1935_ = lean_ctor_get(v___x_1934_, 0);
v_types_1936_ = lean_ctor_get(v___x_1934_, 1);
v_subst_1937_ = lean_ctor_get(v___x_1934_, 2);
v_visitedClosed_1938_ = lean_ctor_get(v___x_1934_, 3);
v_hasDepLetCache_1939_ = lean_ctor_get(v___x_1934_, 4);
v_numConverted_1940_ = lean_ctor_get(v___x_1934_, 5);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1942_ = v___x_1934_;
v_isShared_1943_ = v_isSharedCheck_1950_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_numConverted_1940_);
lean_inc(v_hasDepLetCache_1939_);
lean_inc(v_visitedClosed_1938_);
lean_inc(v_subst_1937_);
lean_inc(v_types_1936_);
lean_inc(v_visited_1935_);
lean_dec(v___x_1934_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1950_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1944_; lean_object* v___x_1946_; 
lean_inc_ref(v_type_1932_);
v___x_1944_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_types_1936_, v_e_1921_, v_type_1932_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 1, v___x_1944_);
v___x_1946_ = v___x_1942_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_visited_1935_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v___x_1944_);
lean_ctor_set(v_reuseFailAlloc_1949_, 2, v_subst_1937_);
lean_ctor_set(v_reuseFailAlloc_1949_, 3, v_visitedClosed_1938_);
lean_ctor_set(v_reuseFailAlloc_1949_, 4, v_hasDepLetCache_1939_);
lean_ctor_set(v_reuseFailAlloc_1949_, 5, v_numConverted_1940_);
v___x_1946_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = lean_st_ref_put(v___y_1933_, v___x_1946_);
v___x_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1948_, 0, v_type_1932_);
return v___x_1948_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1921_ = stack[0].m_obj;
lean_object* v_a_1922_ = stack[1].m_obj;
lean_object* v_a_1923_ = stack[2].m_obj;
lean_object* v_a_1924_ = stack[3].m_obj;
lean_object* v_a_1925_ = stack[4].m_obj;
lean_object* v_a_1926_ = stack[5].m_obj;
lean_object* v_a_1927_ = stack[6].m_obj;
lean_object* v_a_1928_ = stack[7].m_obj;
lean_object* v_a_1929_ = stack[8].m_obj;
lean_object* v_res_2000_;
v_res_2000_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_e_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
stack->m_obj
 = v_res_2000_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___boxed(lean_object* v_e_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_e_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec(v_a_2005_);
lean_dec_ref(v_a_2004_);
lean_dec(v_a_2003_);
lean_dec_ref(v_a_2002_);
return v_res_2011_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(lean_object* v_fvarId_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = l_Lean_Expr_fvar___override(v_fvarId_2012_);
v___x_2016_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2015_, v___y_2013_);
return v___x_2016_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2012_ = stack[0].m_obj;
lean_object* v___y_2013_ = stack[1].m_obj;
lean_object* v_res_2017_;
v_res_2017_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(v_fvarId_2012_, v___y_2013_);
stack->m_obj
 = v_res_2017_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg___boxed(lean_object* v_fvarId_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(v_fvarId_2018_, v___y_2019_);
lean_dec(v___y_2019_);
return v_res_2021_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1(lean_object* v_fvarId_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v___x_2032_; 
v___x_2032_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(v_fvarId_2022_, v___y_2026_);
return v___x_2032_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2022_ = stack[0].m_obj;
lean_object* v___y_2023_ = stack[1].m_obj;
lean_object* v___y_2024_ = stack[2].m_obj;
lean_object* v___y_2025_ = stack[3].m_obj;
lean_object* v___y_2026_ = stack[4].m_obj;
lean_object* v___y_2027_ = stack[5].m_obj;
lean_object* v___y_2028_ = stack[6].m_obj;
lean_object* v___y_2029_ = stack[7].m_obj;
lean_object* v___y_2030_ = stack[8].m_obj;
lean_object* v_res_2033_;
v_res_2033_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1(v_fvarId_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
stack->m_obj
 = v_res_2033_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___boxed(lean_object* v_fvarId_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1(v_fvarId_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
return v_res_2044_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0(lean_object* v_x_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v___x_2055_; 
lean_inc(v___y_2049_);
lean_inc_ref(v___y_2048_);
lean_inc(v___y_2047_);
lean_inc_ref(v___y_2046_);
v___x_2055_ = lean_apply_9(v_x_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, lean_box(0));
return v___x_2055_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2045_ = stack[0].m_obj;
lean_object* v___y_2046_ = stack[1].m_obj;
lean_object* v___y_2047_ = stack[2].m_obj;
lean_object* v___y_2048_ = stack[3].m_obj;
lean_object* v___y_2049_ = stack[4].m_obj;
lean_object* v___y_2050_ = stack[5].m_obj;
lean_object* v___y_2051_ = stack[6].m_obj;
lean_object* v___y_2052_ = stack[7].m_obj;
lean_object* v___y_2053_ = stack[8].m_obj;
lean_object* v_res_2056_;
v_res_2056_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0(v_x_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
stack->m_obj
 = v_res_2056_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0___boxed(lean_object* v_x_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0(v_x_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
return v_res_2067_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(lean_object* v_lctx_2068_, lean_object* v_localInsts_2069_, lean_object* v_x_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v___f_2080_; lean_object* v___x_2081_; 
lean_inc(v___y_2074_);
lean_inc_ref(v___y_2073_);
lean_inc(v___y_2072_);
lean_inc_ref(v___y_2071_);
v___f_2080_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2080_, 0, v_x_2070_);
lean_closure_set(v___f_2080_, 1, v___y_2071_);
lean_closure_set(v___f_2080_, 2, v___y_2072_);
lean_closure_set(v___f_2080_, 3, v___y_2073_);
lean_closure_set(v___f_2080_, 4, v___y_2074_);
v___x_2081_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2068_, v_localInsts_2069_, v___f_2080_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2081_) == 0)
{
return v___x_2081_;
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2081_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_2068_ = stack[0].m_obj;
lean_object* v_localInsts_2069_ = stack[1].m_obj;
lean_object* v_x_2070_ = stack[2].m_obj;
lean_object* v___y_2071_ = stack[3].m_obj;
lean_object* v___y_2072_ = stack[4].m_obj;
lean_object* v___y_2073_ = stack[5].m_obj;
lean_object* v___y_2074_ = stack[6].m_obj;
lean_object* v___y_2075_ = stack[7].m_obj;
lean_object* v___y_2076_ = stack[8].m_obj;
lean_object* v___y_2077_ = stack[9].m_obj;
lean_object* v___y_2078_ = stack[10].m_obj;
lean_object* v_res_2090_;
v_res_2090_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(v_lctx_2068_, v_localInsts_2069_, v_x_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
stack->m_obj
 = v_res_2090_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___boxed(lean_object* v_lctx_2091_, lean_object* v_localInsts_2092_, lean_object* v_x_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(v_lctx_2091_, v_localInsts_2092_, v_x_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
return v_res_2103_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2(lean_object* v_00_u03b1_2104_, lean_object* v_lctx_2105_, lean_object* v_localInsts_2106_, lean_object* v_x_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(v_lctx_2105_, v_localInsts_2106_, v_x_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
return v___x_2117_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_2105_ = stack[1].m_obj;
lean_object* v_localInsts_2106_ = stack[2].m_obj;
lean_object* v_x_2107_ = stack[3].m_obj;
lean_object* v___y_2108_ = stack[4].m_obj;
lean_object* v___y_2109_ = stack[5].m_obj;
lean_object* v___y_2110_ = stack[6].m_obj;
lean_object* v___y_2111_ = stack[7].m_obj;
lean_object* v___y_2112_ = stack[8].m_obj;
lean_object* v___y_2113_ = stack[9].m_obj;
lean_object* v___y_2114_ = stack[10].m_obj;
lean_object* v___y_2115_ = stack[11].m_obj;
lean_object* v_res_2118_;
v_res_2118_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2(lean_box(0), v_lctx_2105_, v_localInsts_2106_, v_x_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
stack->m_obj
 = v_res_2118_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___boxed(lean_object* v_00_u03b1_2119_, lean_object* v_lctx_2120_, lean_object* v_localInsts_2121_, lean_object* v_x_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2(v_00_u03b1_2119_, v_lctx_2120_, v_localInsts_2121_, v_x_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
return v_res_2132_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(lean_object* v___y_2133_, lean_object* v_visited_2134_, lean_object* v_types_2135_, lean_object* v_subst_2136_, lean_object* v_a_x3f_2137_){
_start:
{
lean_object* v___x_2139_; lean_object* v_visitedClosed_2140_; lean_object* v_hasDepLetCache_2141_; lean_object* v_numConverted_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2152_; 
v___x_2139_ = lean_st_ref_take(v___y_2133_);
v_visitedClosed_2140_ = lean_ctor_get(v___x_2139_, 3);
v_hasDepLetCache_2141_ = lean_ctor_get(v___x_2139_, 4);
v_numConverted_2142_ = lean_ctor_get(v___x_2139_, 5);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2152_ == 0)
{
lean_object* v_unused_2153_; lean_object* v_unused_2154_; lean_object* v_unused_2155_; 
v_unused_2153_ = lean_ctor_get(v___x_2139_, 2);
lean_dec(v_unused_2153_);
v_unused_2154_ = lean_ctor_get(v___x_2139_, 1);
lean_dec(v_unused_2154_);
v_unused_2155_ = lean_ctor_get(v___x_2139_, 0);
lean_dec(v_unused_2155_);
v___x_2144_ = v___x_2139_;
v_isShared_2145_ = v_isSharedCheck_2152_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_numConverted_2142_);
lean_inc(v_hasDepLetCache_2141_);
lean_inc(v_visitedClosed_2140_);
lean_dec(v___x_2139_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2152_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2146_ = lean_box(0);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 2, v_subst_2136_);
lean_ctor_set(v___x_2144_, 1, v_types_2135_);
lean_ctor_set(v___x_2144_, 0, v_visited_2134_);
v___x_2148_ = v___x_2144_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_visited_2134_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v_types_2135_);
lean_ctor_set(v_reuseFailAlloc_2151_, 2, v_subst_2136_);
lean_ctor_set(v_reuseFailAlloc_2151_, 3, v_visitedClosed_2140_);
lean_ctor_set(v_reuseFailAlloc_2151_, 4, v_hasDepLetCache_2141_);
lean_ctor_set(v_reuseFailAlloc_2151_, 5, v_numConverted_2142_);
v___x_2148_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = lean_st_ref_put(v___y_2133_, v___x_2148_);
v___x_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2146_);
return v___x_2150_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2133_ = stack[0].m_obj;
lean_object* v_visited_2134_ = stack[1].m_obj;
lean_object* v_types_2135_ = stack[2].m_obj;
lean_object* v_subst_2136_ = stack[3].m_obj;
lean_object* v_a_x3f_2137_ = stack[4].m_obj;
lean_object* v_res_2156_;
v_res_2156_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(v___y_2133_, v_visited_2134_, v_types_2135_, v_subst_2136_, v_a_x3f_2137_);
stack->m_obj
 = v_res_2156_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0___boxed(lean_object* v___y_2157_, lean_object* v_visited_2158_, lean_object* v_types_2159_, lean_object* v_subst_2160_, lean_object* v_a_x3f_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(v___y_2157_, v_visited_2158_, v_types_2159_, v_subst_2160_, v_a_x3f_2161_);
lean_dec(v_a_x3f_2161_);
lean_dec(v___y_2157_);
return v_res_2163_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1(lean_object* v_k_2164_, lean_object* v_a_2165_, uint8_t v_tainted_2166_, uint8_t v_isCandidate_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___y_2178_; lean_object* v_xs_2224_; lean_object* v_numCandidates_2225_; lean_object* v_cleanSuffix_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2245_; 
v_xs_2224_ = lean_ctor_get(v___y_2168_, 0);
v_numCandidates_2225_ = lean_ctor_get(v___y_2168_, 1);
v_cleanSuffix_2226_ = lean_ctor_get(v___y_2168_, 2);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___y_2168_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2228_ = v___y_2168_;
v_isShared_2229_ = v_isSharedCheck_2245_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_cleanSuffix_2226_);
lean_inc(v_numCandidates_2225_);
lean_inc(v_xs_2224_);
lean_dec(v___y_2168_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2245_;
goto v_resetjp_2227_;
}
v___jp_2177_:
{
lean_object* v___x_2179_; lean_object* v_visited_2180_; lean_object* v_types_2181_; lean_object* v_subst_2182_; lean_object* v_visitedClosed_2183_; lean_object* v_hasDepLetCache_2184_; lean_object* v_numConverted_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2223_; 
v___x_2179_ = lean_st_ref_take(v___y_2169_);
v_visited_2180_ = lean_ctor_get(v___x_2179_, 0);
v_types_2181_ = lean_ctor_get(v___x_2179_, 1);
v_subst_2182_ = lean_ctor_get(v___x_2179_, 2);
v_visitedClosed_2183_ = lean_ctor_get(v___x_2179_, 3);
v_hasDepLetCache_2184_ = lean_ctor_get(v___x_2179_, 4);
v_numConverted_2185_ = lean_ctor_get(v___x_2179_, 5);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2187_ = v___x_2179_;
v_isShared_2188_ = v_isSharedCheck_2223_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_numConverted_2185_);
lean_inc(v_hasDepLetCache_2184_);
lean_inc(v_visitedClosed_2183_);
lean_inc(v_subst_2182_);
lean_inc(v_types_2181_);
lean_inc(v_visited_2180_);
lean_dec(v___x_2179_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2223_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2189_; lean_object* v___x_2191_; 
v___x_2189_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 2, v___x_2189_);
lean_ctor_set(v___x_2187_, 1, v___x_2189_);
lean_ctor_set(v___x_2187_, 0, v___x_2189_);
v___x_2191_ = v___x_2187_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2222_, 3, v_visitedClosed_2183_);
lean_ctor_set(v_reuseFailAlloc_2222_, 4, v_hasDepLetCache_2184_);
lean_ctor_set(v_reuseFailAlloc_2222_, 5, v_numConverted_2185_);
v___x_2191_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
lean_object* v___x_2192_; lean_object* v_r_2193_; 
v___x_2192_ = lean_st_ref_put(v___y_2169_, v___x_2191_);
lean_inc(v___y_2175_);
lean_inc_ref(v___y_2174_);
lean_inc(v___y_2173_);
lean_inc_ref(v___y_2172_);
lean_inc(v___y_2171_);
lean_inc_ref(v___y_2170_);
lean_inc(v___y_2169_);
v_r_2193_ = lean_apply_10(v_k_2164_, v_a_2165_, v___y_2178_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, lean_box(0));
if (lean_obj_tag(v_r_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2210_; 
v_a_2194_ = lean_ctor_get(v_r_2193_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v_r_2193_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2196_ = v_r_2193_;
v_isShared_2197_ = v_isSharedCheck_2210_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v_r_2193_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2210_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
lean_inc(v_a_2194_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set_tag(v___x_2196_, 1);
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
lean_object* v___x_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
v___x_2200_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(v___y_2169_, v_visited_2180_, v_types_2181_, v_subst_2182_, v___x_2199_);
lean_dec_ref(v___x_2199_);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2207_ == 0)
{
lean_object* v_unused_2208_; 
v_unused_2208_ = lean_ctor_get(v___x_2200_, 0);
lean_dec(v_unused_2208_);
v___x_2202_ = v___x_2200_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_dec(v___x_2200_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v_a_2194_);
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2194_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
v_a_2211_ = lean_ctor_get(v_r_2193_, 0);
lean_inc(v_a_2211_);
lean_dec_ref_known(v_r_2193_, 1);
v___x_2212_ = lean_box(0);
v___x_2213_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(v___y_2169_, v_visited_2180_, v_types_2181_, v_subst_2182_, v___x_2212_);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; 
v_unused_2221_ = lean_ctor_get(v___x_2213_, 0);
lean_dec(v_unused_2221_);
v___x_2215_ = v___x_2213_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_dec(v___x_2213_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
lean_ctor_set_tag(v___x_2215_, 1);
lean_ctor_set(v___x_2215_, 0, v_a_2211_);
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2211_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
}
v_resetjp_2227_:
{
lean_object* v___x_2230_; lean_object* v___y_2232_; 
lean_inc_ref(v_a_2165_);
v___x_2230_ = l_Lean_PersistentArray_push___redArg(v_xs_2224_, v_a_2165_);
if (v_isCandidate_2167_ == 0)
{
lean_object* v___x_2243_; 
v___x_2243_ = lean_unsigned_to_nat(0u);
v___y_2232_ = v___x_2243_;
goto v___jp_2231_;
}
else
{
lean_object* v___x_2244_; 
v___x_2244_ = lean_unsigned_to_nat(1u);
v___y_2232_ = v___x_2244_;
goto v___jp_2231_;
}
v___jp_2231_:
{
lean_object* v___x_2233_; 
v___x_2233_ = lean_nat_add(v_numCandidates_2225_, v___y_2232_);
lean_dec(v_numCandidates_2225_);
if (v_tainted_2166_ == 0)
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2237_; 
v___x_2234_ = lean_unsigned_to_nat(1u);
v___x_2235_ = lean_nat_add(v_cleanSuffix_2226_, v___x_2234_);
lean_dec(v_cleanSuffix_2226_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 2, v___x_2235_);
lean_ctor_set(v___x_2228_, 1, v___x_2233_);
lean_ctor_set(v___x_2228_, 0, v___x_2230_);
v___x_2237_ = v___x_2228_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2238_, 2, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
v___y_2178_ = v___x_2237_;
goto v___jp_2177_;
}
}
else
{
lean_object* v___x_2239_; lean_object* v___x_2241_; 
lean_dec(v_cleanSuffix_2226_);
v___x_2239_ = lean_unsigned_to_nat(0u);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 2, v___x_2239_);
lean_ctor_set(v___x_2228_, 1, v___x_2233_);
lean_ctor_set(v___x_2228_, 0, v___x_2230_);
v___x_2241_ = v___x_2228_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2242_, 2, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
v___y_2178_ = v___x_2241_;
goto v___jp_2177_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2164_ = stack[0].m_obj;
lean_object* v_a_2165_ = stack[1].m_obj;
uint8_t v_tainted_2166_ = stack[2].m_num;
uint8_t v_isCandidate_2167_ = stack[3].m_num;
lean_object* v___y_2168_ = stack[4].m_obj;
lean_object* v___y_2169_ = stack[5].m_obj;
lean_object* v___y_2170_ = stack[6].m_obj;
lean_object* v___y_2171_ = stack[7].m_obj;
lean_object* v___y_2172_ = stack[8].m_obj;
lean_object* v___y_2173_ = stack[9].m_obj;
lean_object* v___y_2174_ = stack[10].m_obj;
lean_object* v___y_2175_ = stack[11].m_obj;
lean_object* v_res_2246_;
v_res_2246_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1(v_k_2164_, v_a_2165_, v_tainted_2166_, v_isCandidate_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
stack->m_obj
 = v_res_2246_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1___boxed(lean_object* v_k_2247_, lean_object* v_a_2248_, lean_object* v_tainted_2249_, lean_object* v_isCandidate_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
uint8_t v_tainted_boxed_2260_; uint8_t v_isCandidate_boxed_2261_; lean_object* v_res_2262_; 
v_tainted_boxed_2260_ = lean_unbox(v_tainted_2249_);
v_isCandidate_boxed_2261_ = lean_unbox(v_isCandidate_2250_);
v_res_2262_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1(v_k_2247_, v_a_2248_, v_tainted_boxed_2260_, v_isCandidate_boxed_2261_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
return v_res_2262_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg(lean_object* v___y_2263_){
_start:
{
lean_object* v___x_2265_; lean_object* v_ngen_2266_; lean_object* v_namePrefix_2267_; lean_object* v_idx_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2298_; 
v___x_2265_ = lean_st_ref_get(v___y_2263_);
v_ngen_2266_ = lean_ctor_get(v___x_2265_, 2);
lean_inc_ref(v_ngen_2266_);
lean_dec(v___x_2265_);
v_namePrefix_2267_ = lean_ctor_get(v_ngen_2266_, 0);
v_idx_2268_ = lean_ctor_get(v_ngen_2266_, 1);
v_isSharedCheck_2298_ = !lean_is_exclusive(v_ngen_2266_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2270_ = v_ngen_2266_;
v_isShared_2271_ = v_isSharedCheck_2298_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_idx_2268_);
lean_inc(v_namePrefix_2267_);
lean_dec(v_ngen_2266_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2298_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v_r_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
lean_inc(v_idx_2268_);
lean_inc(v_namePrefix_2267_);
v_r_2272_ = l_Lean_Name_num___override(v_namePrefix_2267_, v_idx_2268_);
v___x_2273_ = lean_unsigned_to_nat(1u);
v___x_2274_ = lean_nat_add(v_idx_2268_, v___x_2273_);
lean_dec(v_idx_2268_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 1, v___x_2274_);
v___x_2276_ = v___x_2270_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_namePrefix_2267_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
lean_object* v___x_2277_; lean_object* v_env_2278_; lean_object* v_nextMacroScope_2279_; lean_object* v_auxDeclNGen_2280_; lean_object* v_traceState_2281_; lean_object* v_cache_2282_; lean_object* v_recordedDeps_2283_; lean_object* v_messages_2284_; lean_object* v_infoState_2285_; lean_object* v_snapshotTasks_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2295_; 
v___x_2277_ = lean_st_ref_take(v___y_2263_);
v_env_2278_ = lean_ctor_get(v___x_2277_, 0);
v_nextMacroScope_2279_ = lean_ctor_get(v___x_2277_, 1);
v_auxDeclNGen_2280_ = lean_ctor_get(v___x_2277_, 3);
v_traceState_2281_ = lean_ctor_get(v___x_2277_, 4);
v_cache_2282_ = lean_ctor_get(v___x_2277_, 5);
v_recordedDeps_2283_ = lean_ctor_get(v___x_2277_, 6);
v_messages_2284_ = lean_ctor_get(v___x_2277_, 7);
v_infoState_2285_ = lean_ctor_get(v___x_2277_, 8);
v_snapshotTasks_2286_ = lean_ctor_get(v___x_2277_, 9);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2295_ == 0)
{
lean_object* v_unused_2296_; 
v_unused_2296_ = lean_ctor_get(v___x_2277_, 2);
lean_dec(v_unused_2296_);
v___x_2288_ = v___x_2277_;
v_isShared_2289_ = v_isSharedCheck_2295_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_snapshotTasks_2286_);
lean_inc(v_infoState_2285_);
lean_inc(v_messages_2284_);
lean_inc(v_recordedDeps_2283_);
lean_inc(v_cache_2282_);
lean_inc(v_traceState_2281_);
lean_inc(v_auxDeclNGen_2280_);
lean_inc(v_nextMacroScope_2279_);
lean_inc(v_env_2278_);
lean_dec(v___x_2277_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2295_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 2, v___x_2276_);
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_env_2278_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v_nextMacroScope_2279_);
lean_ctor_set(v_reuseFailAlloc_2294_, 2, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2294_, 3, v_auxDeclNGen_2280_);
lean_ctor_set(v_reuseFailAlloc_2294_, 4, v_traceState_2281_);
lean_ctor_set(v_reuseFailAlloc_2294_, 5, v_cache_2282_);
lean_ctor_set(v_reuseFailAlloc_2294_, 6, v_recordedDeps_2283_);
lean_ctor_set(v_reuseFailAlloc_2294_, 7, v_messages_2284_);
lean_ctor_set(v_reuseFailAlloc_2294_, 8, v_infoState_2285_);
lean_ctor_set(v_reuseFailAlloc_2294_, 9, v_snapshotTasks_2286_);
v___x_2291_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = lean_st_ref_put(v___y_2263_, v___x_2291_);
v___x_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2293_, 0, v_r_2272_);
return v___x_2293_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2263_ = stack[0].m_obj;
lean_object* v_res_2299_;
v_res_2299_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg(v___y_2263_);
stack->m_obj
 = v_res_2299_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg___boxed(lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg(v___y_2300_);
lean_dec(v___y_2300_);
return v_res_2302_;
}
}
lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0(lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v___x_2312_; lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
v___x_2312_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg(v___y_2310_);
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2303_ = stack[0].m_obj;
lean_object* v___y_2304_ = stack[1].m_obj;
lean_object* v___y_2305_ = stack[2].m_obj;
lean_object* v___y_2306_ = stack[3].m_obj;
lean_object* v___y_2307_ = stack[4].m_obj;
lean_object* v___y_2308_ = stack[5].m_obj;
lean_object* v___y_2309_ = stack[6].m_obj;
lean_object* v___y_2310_ = stack[7].m_obj;
lean_object* v_res_2321_;
v_res_2321_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0(v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
stack->m_obj
 = v_res_2321_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0___boxed(lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0(v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
return v_res_2331_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(lean_object* v_n_2334_, lean_object* v_type_2335_, lean_object* v_value_x3f_2336_, uint8_t v_tainted_2337_, uint8_t v_isCandidate_2338_, lean_object* v_k_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0(v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2351_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc_n(v_a_2350_, 2);
lean_dec_ref_known(v___x_2349_, 1);
v___x_2351_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(v_a_2350_, v_a_2343_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v_lctx_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___f_2356_; lean_object* v___y_2358_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2351_, 1);
v_lctx_2353_ = lean_ctor_get(v_a_2344_, 2);
v___x_2354_ = lean_box(v_tainted_2337_);
v___x_2355_ = lean_box(v_isCandidate_2338_);
v___f_2356_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2356_, 0, v_k_2339_);
lean_closure_set(v___f_2356_, 1, v_a_2352_);
lean_closure_set(v___f_2356_, 2, v___x_2354_);
lean_closure_set(v___f_2356_, 3, v___x_2355_);
if (lean_obj_tag(v_value_x3f_2336_) == 0)
{
uint8_t v___x_2361_; uint8_t v___x_2362_; lean_object* v___x_2363_; 
v___x_2361_ = 0;
v___x_2362_ = 0;
lean_inc_ref(v_lctx_2353_);
v___x_2363_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2353_, v_a_2350_, v_n_2334_, v_type_2335_, v___x_2361_, v___x_2362_);
v___y_2358_ = v___x_2363_;
goto v___jp_2357_;
}
else
{
lean_object* v_val_2364_; lean_object* v_fst_2365_; lean_object* v_snd_2366_; uint8_t v___x_2367_; uint8_t v___x_2368_; lean_object* v___x_2369_; 
v_val_2364_ = lean_ctor_get(v_value_x3f_2336_, 0);
lean_inc(v_val_2364_);
lean_dec_ref_known(v_value_x3f_2336_, 1);
v_fst_2365_ = lean_ctor_get(v_val_2364_, 0);
lean_inc(v_fst_2365_);
v_snd_2366_ = lean_ctor_get(v_val_2364_, 1);
lean_inc(v_snd_2366_);
lean_dec(v_val_2364_);
v___x_2367_ = 0;
v___x_2368_ = lean_unbox(v_snd_2366_);
lean_dec(v_snd_2366_);
lean_inc_ref(v_lctx_2353_);
v___x_2369_ = l_Lean_LocalContext_mkLetDecl(v_lctx_2353_, v_a_2350_, v_n_2334_, v_type_2335_, v_fst_2365_, v___x_2368_, v___x_2367_);
v___y_2358_ = v___x_2369_;
goto v___jp_2357_;
}
v___jp_2357_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___closed__0));
v___x_2360_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(v___y_2358_, v___x_2359_, v___f_2356_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
return v___x_2360_;
}
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
lean_dec(v_a_2350_);
lean_dec_ref(v_k_2339_);
lean_dec(v_value_x3f_2336_);
lean_dec_ref(v_type_2335_);
lean_dec(v_n_2334_);
v_a_2370_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2351_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2351_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
lean_dec_ref(v_k_2339_);
lean_dec(v_value_x3f_2336_);
lean_dec_ref(v_type_2335_);
lean_dec(v_n_2334_);
v_a_2378_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2349_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2349_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2334_ = stack[0].m_obj;
lean_object* v_type_2335_ = stack[1].m_obj;
lean_object* v_value_x3f_2336_ = stack[2].m_obj;
uint8_t v_tainted_2337_ = stack[3].m_num;
uint8_t v_isCandidate_2338_ = stack[4].m_num;
lean_object* v_k_2339_ = stack[5].m_obj;
lean_object* v_a_2340_ = stack[6].m_obj;
lean_object* v_a_2341_ = stack[7].m_obj;
lean_object* v_a_2342_ = stack[8].m_obj;
lean_object* v_a_2343_ = stack[9].m_obj;
lean_object* v_a_2344_ = stack[10].m_obj;
lean_object* v_a_2345_ = stack[11].m_obj;
lean_object* v_a_2346_ = stack[12].m_obj;
lean_object* v_a_2347_ = stack[13].m_obj;
lean_object* v_res_2386_;
v_res_2386_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_n_2334_, v_type_2335_, v_value_x3f_2336_, v_tainted_2337_, v_isCandidate_2338_, v_k_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
stack->m_obj
 = v_res_2386_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___boxed(lean_object* v_n_2387_, lean_object* v_type_2388_, lean_object* v_value_x3f_2389_, lean_object* v_tainted_2390_, lean_object* v_isCandidate_2391_, lean_object* v_k_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_){
_start:
{
uint8_t v_tainted_boxed_2402_; uint8_t v_isCandidate_boxed_2403_; lean_object* v_res_2404_; 
v_tainted_boxed_2402_ = lean_unbox(v_tainted_2390_);
v_isCandidate_boxed_2403_ = lean_unbox(v_isCandidate_2391_);
v_res_2404_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_n_2387_, v_type_2388_, v_value_x3f_2389_, v_tainted_boxed_2402_, v_isCandidate_boxed_2403_, v_k_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
return v_res_2404_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder(lean_object* v_00_u03b1_2405_, lean_object* v_n_2406_, lean_object* v_type_2407_, lean_object* v_value_x3f_2408_, uint8_t v_tainted_2409_, uint8_t v_isCandidate_2410_, lean_object* v_k_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_n_2406_, v_type_2407_, v_value_x3f_2408_, v_tainted_2409_, v_isCandidate_2410_, v_k_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
return v___x_2421_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2406_ = stack[1].m_obj;
lean_object* v_type_2407_ = stack[2].m_obj;
lean_object* v_value_x3f_2408_ = stack[3].m_obj;
uint8_t v_tainted_2409_ = stack[4].m_num;
uint8_t v_isCandidate_2410_ = stack[5].m_num;
lean_object* v_k_2411_ = stack[6].m_obj;
lean_object* v_a_2412_ = stack[7].m_obj;
lean_object* v_a_2413_ = stack[8].m_obj;
lean_object* v_a_2414_ = stack[9].m_obj;
lean_object* v_a_2415_ = stack[10].m_obj;
lean_object* v_a_2416_ = stack[11].m_obj;
lean_object* v_a_2417_ = stack[12].m_obj;
lean_object* v_a_2418_ = stack[13].m_obj;
lean_object* v_a_2419_ = stack[14].m_obj;
lean_object* v_res_2422_;
v_res_2422_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder(lean_box(0), v_n_2406_, v_type_2407_, v_value_x3f_2408_, v_tainted_2409_, v_isCandidate_2410_, v_k_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
stack->m_obj
 = v_res_2422_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___boxed(lean_object* v_00_u03b1_2423_, lean_object* v_n_2424_, lean_object* v_type_2425_, lean_object* v_value_x3f_2426_, lean_object* v_tainted_2427_, lean_object* v_isCandidate_2428_, lean_object* v_k_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
uint8_t v_tainted_boxed_2439_; uint8_t v_isCandidate_boxed_2440_; lean_object* v_res_2441_; 
v_tainted_boxed_2439_ = lean_unbox(v_tainted_2427_);
v_isCandidate_boxed_2440_ = lean_unbox(v_isCandidate_2428_);
v_res_2441_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder(v_00_u03b1_2423_, v_n_2424_, v_type_2425_, v_value_x3f_2426_, v_tainted_boxed_2439_, v_isCandidate_boxed_2440_, v_k_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
return v_res_2441_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0(lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg(v___y_2449_);
return v___x_2451_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2442_ = stack[0].m_obj;
lean_object* v___y_2443_ = stack[1].m_obj;
lean_object* v___y_2444_ = stack[2].m_obj;
lean_object* v___y_2445_ = stack[3].m_obj;
lean_object* v___y_2446_ = stack[4].m_obj;
lean_object* v___y_2447_ = stack[5].m_obj;
lean_object* v___y_2448_ = stack[6].m_obj;
lean_object* v___y_2449_ = stack[7].m_obj;
lean_object* v_res_2452_;
v_res_2452_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0(v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
stack->m_obj
 = v_res_2452_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___boxed(lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0(v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
return v_res_2462_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0(lean_object* v_msg_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v_toApplicative_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2540_; 
v___x_2473_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0);
v___x_2474_ = l_StateRefT_x27_instMonad___redArg(v___x_2473_);
v_toApplicative_2475_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2540_ == 0)
{
lean_object* v_unused_2541_; 
v_unused_2541_ = lean_ctor_get(v___x_2474_, 1);
lean_dec(v_unused_2541_);
v___x_2477_ = v___x_2474_;
v_isShared_2478_ = v_isSharedCheck_2540_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_toApplicative_2475_);
lean_dec(v___x_2474_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2540_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v_toFunctor_2479_; lean_object* v_toSeq_2480_; lean_object* v_toSeqLeft_2481_; lean_object* v_toSeqRight_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2538_; 
v_toFunctor_2479_ = lean_ctor_get(v_toApplicative_2475_, 0);
v_toSeq_2480_ = lean_ctor_get(v_toApplicative_2475_, 2);
v_toSeqLeft_2481_ = lean_ctor_get(v_toApplicative_2475_, 3);
v_toSeqRight_2482_ = lean_ctor_get(v_toApplicative_2475_, 4);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_toApplicative_2475_);
if (v_isSharedCheck_2538_ == 0)
{
lean_object* v_unused_2539_; 
v_unused_2539_ = lean_ctor_get(v_toApplicative_2475_, 1);
lean_dec(v_unused_2539_);
v___x_2484_ = v_toApplicative_2475_;
v_isShared_2485_ = v_isSharedCheck_2538_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_toSeqRight_2482_);
lean_inc(v_toSeqLeft_2481_);
lean_inc(v_toSeq_2480_);
lean_inc(v_toFunctor_2479_);
lean_dec(v_toApplicative_2475_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2538_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___f_2486_; lean_object* v___f_2487_; lean_object* v___f_2488_; lean_object* v___f_2489_; lean_object* v___x_2490_; lean_object* v___f_2491_; lean_object* v___f_2492_; lean_object* v___f_2493_; lean_object* v___x_2495_; 
v___f_2486_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__1));
v___f_2487_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__2));
lean_inc_ref(v_toFunctor_2479_);
v___f_2488_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2488_, 0, v_toFunctor_2479_);
v___f_2489_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2489_, 0, v_toFunctor_2479_);
v___x_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___f_2488_);
lean_ctor_set(v___x_2490_, 1, v___f_2489_);
v___f_2491_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2491_, 0, v_toSeqRight_2482_);
v___f_2492_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2492_, 0, v_toSeqLeft_2481_);
v___f_2493_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2493_, 0, v_toSeq_2480_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 4, v___f_2491_);
lean_ctor_set(v___x_2484_, 3, v___f_2492_);
lean_ctor_set(v___x_2484_, 2, v___f_2493_);
lean_ctor_set(v___x_2484_, 1, v___f_2486_);
lean_ctor_set(v___x_2484_, 0, v___x_2490_);
v___x_2495_ = v___x_2484_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v___f_2486_);
lean_ctor_set(v_reuseFailAlloc_2537_, 2, v___f_2493_);
lean_ctor_set(v_reuseFailAlloc_2537_, 3, v___f_2492_);
lean_ctor_set(v_reuseFailAlloc_2537_, 4, v___f_2491_);
v___x_2495_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
lean_object* v___x_2497_; 
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 1, v___f_2487_);
lean_ctor_set(v___x_2477_, 0, v___x_2495_);
v___x_2497_ = v___x_2477_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2495_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v___f_2487_);
v___x_2497_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
lean_object* v___x_2498_; lean_object* v_toApplicative_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2534_; 
v___x_2498_ = l_StateRefT_x27_instMonad___redArg(v___x_2497_);
v_toApplicative_2499_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2534_ == 0)
{
lean_object* v_unused_2535_; 
v_unused_2535_ = lean_ctor_get(v___x_2498_, 1);
lean_dec(v_unused_2535_);
v___x_2501_ = v___x_2498_;
v_isShared_2502_ = v_isSharedCheck_2534_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_toApplicative_2499_);
lean_dec(v___x_2498_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2534_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v_toFunctor_2503_; lean_object* v_toSeq_2504_; lean_object* v_toSeqLeft_2505_; lean_object* v_toSeqRight_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2532_; 
v_toFunctor_2503_ = lean_ctor_get(v_toApplicative_2499_, 0);
v_toSeq_2504_ = lean_ctor_get(v_toApplicative_2499_, 2);
v_toSeqLeft_2505_ = lean_ctor_get(v_toApplicative_2499_, 3);
v_toSeqRight_2506_ = lean_ctor_get(v_toApplicative_2499_, 4);
v_isSharedCheck_2532_ = !lean_is_exclusive(v_toApplicative_2499_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; 
v_unused_2533_ = lean_ctor_get(v_toApplicative_2499_, 1);
lean_dec(v_unused_2533_);
v___x_2508_ = v_toApplicative_2499_;
v_isShared_2509_ = v_isSharedCheck_2532_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_toSeqRight_2506_);
lean_inc(v_toSeqLeft_2505_);
lean_inc(v_toSeq_2504_);
lean_inc(v_toFunctor_2503_);
lean_dec(v_toApplicative_2499_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2532_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___f_2510_; lean_object* v___f_2511_; lean_object* v___f_2512_; lean_object* v___f_2513_; lean_object* v___x_2514_; lean_object* v___f_2515_; lean_object* v___f_2516_; lean_object* v___f_2517_; lean_object* v___x_2519_; 
v___f_2510_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__3));
v___f_2511_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__4));
lean_inc_ref(v_toFunctor_2503_);
v___f_2512_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2512_, 0, v_toFunctor_2503_);
v___f_2513_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2513_, 0, v_toFunctor_2503_);
v___x_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___f_2512_);
lean_ctor_set(v___x_2514_, 1, v___f_2513_);
v___f_2515_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2515_, 0, v_toSeqRight_2506_);
v___f_2516_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2516_, 0, v_toSeqLeft_2505_);
v___f_2517_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2517_, 0, v_toSeq_2504_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 4, v___f_2515_);
lean_ctor_set(v___x_2508_, 3, v___f_2516_);
lean_ctor_set(v___x_2508_, 2, v___f_2517_);
lean_ctor_set(v___x_2508_, 1, v___f_2510_);
lean_ctor_set(v___x_2508_, 0, v___x_2514_);
v___x_2519_ = v___x_2508_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2514_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v___f_2510_);
lean_ctor_set(v_reuseFailAlloc_2531_, 2, v___f_2517_);
lean_ctor_set(v_reuseFailAlloc_2531_, 3, v___f_2516_);
lean_ctor_set(v_reuseFailAlloc_2531_, 4, v___f_2515_);
v___x_2519_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
lean_object* v___x_2521_; 
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v___f_2511_);
lean_ctor_set(v___x_2501_, 0, v___x_2519_);
v___x_2521_ = v___x_2501_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2519_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v___f_2511_);
v___x_2521_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___f_2527_; lean_object* v___x_5541__overap_2528_; lean_object* v___x_2529_; 
v___x_2522_ = l_StateRefT_x27_instMonad___redArg(v___x_2521_);
v___x_2523_ = l_ReaderT_instMonad___redArg(v___x_2522_);
v___x_2524_ = l_StateRefT_x27_instMonad___redArg(v___x_2523_);
v___x_2525_ = lean_box(0);
v___x_2526_ = l_instInhabitedOfMonad___redArg(v___x_2524_, v___x_2525_);
v___f_2527_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2527_, 0, v___x_2526_);
v___x_5541__overap_2528_ = lean_panic_fn_borrowed(v___f_2527_, v_msg_2463_);
lean_dec_ref(v___f_2527_);
lean_inc(v___y_2471_);
lean_inc_ref(v___y_2470_);
lean_inc(v___y_2469_);
lean_inc_ref(v___y_2468_);
lean_inc(v___y_2467_);
lean_inc_ref(v___y_2466_);
lean_inc(v___y_2465_);
lean_inc_ref(v___y_2464_);
v___x_2529_ = lean_apply_9(v___x_5541__overap_2528_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, lean_box(0));
return v___x_2529_;
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
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2463_ = stack[0].m_obj;
lean_object* v___y_2464_ = stack[1].m_obj;
lean_object* v___y_2465_ = stack[2].m_obj;
lean_object* v___y_2466_ = stack[3].m_obj;
lean_object* v___y_2467_ = stack[4].m_obj;
lean_object* v___y_2468_ = stack[5].m_obj;
lean_object* v___y_2469_ = stack[6].m_obj;
lean_object* v___y_2470_ = stack[7].m_obj;
lean_object* v___y_2471_ = stack[8].m_obj;
lean_object* v_res_2542_;
v_res_2542_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0(v_msg_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
stack->m_obj
 = v_res_2542_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0___boxed(lean_object* v_msg_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0(v_msg_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0___boxed(lean_object* v_body_2554_, lean_object* v_body_2555_, lean_object* v_x_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0(v_body_2554_, v_body_2555_, v_x_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec_ref(v_x_2556_);
return v_res_2566_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__1(void){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2568_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_2569_ = lean_unsigned_to_nat(42u);
v___x_2570_ = lean_unsigned_to_nat(340u);
v___x_2571_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__0));
v___x_2572_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0));
v___x_2573_ = l_mkPanicMessageWithDecl(v___x_2572_, v___x_2571_, v___x_2570_, v___x_2569_, v___x_2568_);
return v___x_2573_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(lean_object* v_e_2574_, lean_object* v_expected_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_){
_start:
{
if (lean_obj_tag(v_e_2574_) == 6)
{
lean_object* v_binderName_2585_; lean_object* v_binderType_2586_; lean_object* v_body_2587_; lean_object* v___x_2588_; 
v_binderName_2585_ = lean_ctor_get(v_e_2574_, 0);
lean_inc(v_binderName_2585_);
v_binderType_2586_ = lean_ctor_get(v_e_2574_, 1);
lean_inc_ref(v_binderType_2586_);
v_body_2587_ = lean_ctor_get(v_e_2574_, 2);
lean_inc_ref(v_body_2587_);
lean_dec_ref_known(v_e_2574_, 3);
v___x_2588_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_expected_2575_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v___x_2588_, 1);
if (lean_obj_tag(v_a_2589_) == 7)
{
lean_object* v_binderType_2590_; lean_object* v_body_2591_; lean_object* v___f_2592_; lean_object* v___x_2593_; 
v_binderType_2590_ = lean_ctor_get(v_a_2589_, 1);
lean_inc_ref(v_binderType_2590_);
v_body_2591_ = lean_ctor_get(v_a_2589_, 2);
lean_inc_ref(v_body_2591_);
lean_dec_ref_known(v_a_2589_, 3);
v___f_2592_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0___boxed), 12, 2);
lean_closure_set(v___f_2592_, 0, v_body_2591_);
lean_closure_set(v___f_2592_, 1, v_body_2587_);
lean_inc_ref(v_binderType_2586_);
v___x_2593_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_binderType_2586_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2595_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc_n(v_a_2594_, 2);
lean_dec_ref_known(v___x_2593_, 1);
v___x_2595_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_a_2594_, v_binderType_2590_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_cleanSuffix_2596_; lean_object* v___x_2597_; uint8_t v___y_2599_; lean_object* v___x_2602_; uint8_t v___x_2603_; 
lean_dec_ref_known(v___x_2595_, 1);
v_cleanSuffix_2596_ = lean_ctor_get(v_a_2576_, 2);
v___x_2597_ = lean_box(0);
v___x_2602_ = l_Lean_Expr_looseBVarRange(v_binderType_2586_);
lean_dec_ref(v_binderType_2586_);
v___x_2603_ = lean_nat_dec_le(v___x_2602_, v_cleanSuffix_2596_);
lean_dec(v___x_2602_);
if (v___x_2603_ == 0)
{
uint8_t v___x_2604_; 
v___x_2604_ = 1;
v___y_2599_ = v___x_2604_;
goto v___jp_2598_;
}
else
{
uint8_t v___x_2605_; 
v___x_2605_ = 0;
v___y_2599_ = v___x_2605_;
goto v___jp_2598_;
}
v___jp_2598_:
{
uint8_t v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = 0;
v___x_2601_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_binderName_2585_, v_a_2594_, v___x_2597_, v___y_2599_, v___x_2600_, v___f_2592_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_);
return v___x_2601_;
}
}
else
{
lean_dec(v_a_2594_);
lean_dec_ref(v___f_2592_);
lean_dec_ref(v_binderType_2586_);
lean_dec(v_binderName_2585_);
return v___x_2595_;
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec_ref(v___f_2592_);
lean_dec_ref(v_binderType_2590_);
lean_dec_ref(v_binderType_2586_);
lean_dec(v_binderName_2585_);
v_a_2606_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2593_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2593_);
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
else
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
lean_dec(v_a_2589_);
lean_dec_ref(v_body_2587_);
lean_dec_ref(v_binderType_2586_);
lean_dec(v_binderName_2585_);
v___x_2614_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__1);
v___x_2615_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0(v___x_2614_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_);
return v___x_2615_;
}
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec_ref(v_body_2587_);
lean_dec_ref(v_binderType_2586_);
lean_dec(v_binderName_2585_);
v_a_2616_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2588_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2588_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
else
{
lean_object* v___x_2624_; 
v___x_2624_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_e_2574_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; lean_object* v___x_2626_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_a_2625_);
lean_dec_ref_known(v___x_2624_, 1);
v___x_2626_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_a_2625_, v_expected_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_);
return v___x_2626_;
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec_ref(v_expected_2575_);
v_a_2627_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2624_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2624_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2574_ = stack[0].m_obj;
lean_object* v_expected_2575_ = stack[1].m_obj;
lean_object* v_a_2576_ = stack[2].m_obj;
lean_object* v_a_2577_ = stack[3].m_obj;
lean_object* v_a_2578_ = stack[4].m_obj;
lean_object* v_a_2579_ = stack[5].m_obj;
lean_object* v_a_2580_ = stack[6].m_obj;
lean_object* v_a_2581_ = stack[7].m_obj;
lean_object* v_a_2582_ = stack[8].m_obj;
lean_object* v_a_2583_ = stack[9].m_obj;
lean_object* v_res_2635_;
v_res_2635_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_e_2574_, v_expected_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_);
stack->m_obj
 = v_res_2635_;
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0(lean_object* v_body_2636_, lean_object* v_body_2637_, lean_object* v_x_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
uint8_t v___x_2648_; 
v___x_2648_ = l_Lean_Expr_hasLooseBVars(v_body_2636_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2649_; 
v___x_2649_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_body_2637_, v_body_2636_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
return v___x_2649_;
}
else
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = lean_expr_instantiate1(v_body_2636_, v_x_2638_);
lean_dec_ref(v_body_2636_);
v___x_2651_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2650_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; lean_object* v___x_2653_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref_known(v___x_2651_, 1);
v___x_2653_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_body_2637_, v_a_2652_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
return v___x_2653_;
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec_ref(v_body_2637_);
v_a_2654_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2651_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2651_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_2636_ = stack[0].m_obj;
lean_object* v_body_2637_ = stack[1].m_obj;
lean_object* v_x_2638_ = stack[2].m_obj;
lean_object* v___y_2639_ = stack[3].m_obj;
lean_object* v___y_2640_ = stack[4].m_obj;
lean_object* v___y_2641_ = stack[5].m_obj;
lean_object* v___y_2642_ = stack[6].m_obj;
lean_object* v___y_2643_ = stack[7].m_obj;
lean_object* v___y_2644_ = stack[8].m_obj;
lean_object* v___y_2645_ = stack[9].m_obj;
lean_object* v___y_2646_ = stack[10].m_obj;
lean_object* v_res_2662_;
v_res_2662_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0(v_body_2636_, v_body_2637_, v_x_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
stack->m_obj
 = v_res_2662_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___boxed(lean_object* v_e_2663_, lean_object* v_expected_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_e_2663_, v_expected_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
lean_dec(v_a_2672_);
lean_dec_ref(v_a_2671_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
return v_res_2674_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(lean_object* v_t_2675_, lean_object* v_tf_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
lean_object* v_numCandidates_2686_; lean_object* v_cleanSuffix_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; 
v_numCandidates_2686_ = lean_ctor_get(v_a_2677_, 1);
v_cleanSuffix_2687_ = lean_ctor_get(v_a_2677_, 2);
v___x_2688_ = lean_unsigned_to_nat(0u);
v___x_2689_ = lean_nat_dec_lt(v___x_2688_, v_numCandidates_2686_);
if (v___x_2689_ == 0)
{
lean_dec_ref(v_tf_2676_);
goto v___jp_2683_;
}
else
{
lean_object* v___x_2690_; uint8_t v___x_2691_; 
v___x_2690_ = l_Lean_Expr_looseBVarRange(v_t_2675_);
v___x_2691_ = lean_nat_dec_le(v___x_2690_, v_cleanSuffix_2687_);
lean_dec(v___x_2690_);
if (v___x_2691_ == 0)
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2692_ = lean_box(0);
v___x_2693_ = l_Lean_Meta_getLevel(v_tf_2676_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2700_ == 0)
{
lean_object* v_unused_2701_; 
v_unused_2701_ = lean_ctor_get(v___x_2693_, 0);
lean_dec(v_unused_2701_);
v___x_2695_ = v___x_2693_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_dec(v___x_2693_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 0, v___x_2692_);
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2692_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
v_a_2702_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2693_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2693_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
else
{
lean_dec_ref(v_tf_2676_);
goto v___jp_2683_;
}
}
v___jp_2683_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2684_ = lean_box(0);
v___x_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
return v___x_2685_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2675_ = stack[0].m_obj;
lean_object* v_tf_2676_ = stack[1].m_obj;
lean_object* v_a_2677_ = stack[2].m_obj;
lean_object* v_a_2678_ = stack[3].m_obj;
lean_object* v_a_2679_ = stack[4].m_obj;
lean_object* v_a_2680_ = stack[5].m_obj;
lean_object* v_a_2681_ = stack[6].m_obj;
lean_object* v_res_2710_;
v_res_2710_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_t_2675_, v_tf_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
stack->m_obj
 = v_res_2710_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg___boxed(lean_object* v_t_2711_, lean_object* v_tf_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_t_2711_, v_tf_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec_ref(v_t_2711_);
return v_res_2719_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain(lean_object* v_t_2720_, lean_object* v_tf_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_t_2720_, v_tf_2721_, v_a_2722_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
return v___x_2731_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2720_ = stack[0].m_obj;
lean_object* v_tf_2721_ = stack[1].m_obj;
lean_object* v_a_2722_ = stack[2].m_obj;
lean_object* v_a_2723_ = stack[3].m_obj;
lean_object* v_a_2724_ = stack[4].m_obj;
lean_object* v_a_2725_ = stack[5].m_obj;
lean_object* v_a_2726_ = stack[6].m_obj;
lean_object* v_a_2727_ = stack[7].m_obj;
lean_object* v_a_2728_ = stack[8].m_obj;
lean_object* v_a_2729_ = stack[9].m_obj;
lean_object* v_res_2732_;
v_res_2732_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain(v_t_2720_, v_tf_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
stack->m_obj
 = v_res_2732_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___boxed(lean_object* v_t_2733_, lean_object* v_tf_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain(v_t_2733_, v_tf_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_);
lean_dec(v_a_2742_);
lean_dec_ref(v_a_2741_);
lean_dec(v_a_2740_);
lean_dec_ref(v_a_2739_);
lean_dec(v_a_2738_);
lean_dec_ref(v_a_2737_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
lean_dec_ref(v_t_2733_);
return v_res_2744_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1(void){
_start:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2746_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_2747_ = lean_unsigned_to_nat(35u);
v___x_2748_ = lean_unsigned_to_nat(322u);
v___x_2749_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__0));
v___x_2750_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0));
v___x_2751_ = l_mkPanicMessageWithDecl(v___x_2750_, v___x_2749_, v___x_2748_, v___x_2747_, v___x_2746_);
return v___x_2751_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp(lean_object* v_f_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_f_2752_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2765_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2764_);
lean_dec_ref_known(v___x_2763_, 1);
v___x_2765_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_a_2764_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2793_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2768_ = v___x_2765_;
v_isShared_2769_ = v_isSharedCheck_2793_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2765_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2793_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
if (lean_obj_tag(v_a_2766_) == 7)
{
lean_object* v_binderType_2770_; uint8_t v___x_2785_; 
v_binderType_2770_ = lean_ctor_get(v_a_2766_, 1);
lean_inc_ref(v_binderType_2770_);
lean_dec_ref_known(v_a_2766_, 3);
v___x_2785_ = l_Lean_Expr_hasLooseBVars(v_a_2753_);
if (v___x_2785_ == 0)
{
uint8_t v___x_2786_; 
v___x_2786_ = l_Lean_Expr_hasFVar(v_binderType_2770_);
if (v___x_2786_ == 0)
{
lean_object* v___x_2787_; lean_object* v___x_2789_; 
lean_dec_ref(v_binderType_2770_);
lean_dec_ref(v_a_2753_);
v___x_2787_ = lean_box(0);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 0, v___x_2787_);
v___x_2789_ = v___x_2768_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2787_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
else
{
lean_del_object(v___x_2768_);
goto v___jp_2771_;
}
}
else
{
lean_del_object(v___x_2768_);
goto v___jp_2771_;
}
v___jp_2771_:
{
uint8_t v___x_2772_; 
v___x_2772_ = l_Lean_Expr_isLambda(v_a_2753_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; 
v___x_2773_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2775_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2773_, 1);
v___x_2775_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_a_2774_, v_binderType_2770_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_);
return v___x_2775_;
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_dec_ref(v_binderType_2770_);
v_a_2776_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2773_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2773_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
else
{
lean_object* v___x_2784_; 
v___x_2784_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_a_2753_, v_binderType_2770_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_);
return v___x_2784_;
}
}
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
lean_del_object(v___x_2768_);
lean_dec(v_a_2766_);
lean_dec_ref(v_a_2753_);
v___x_2791_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1);
v___x_2792_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0(v___x_2791_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_);
return v___x_2792_;
}
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_dec_ref(v_a_2753_);
v_a_2794_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2765_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2765_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec_ref(v_a_2753_);
v_a_2802_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2763_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2763_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2752_ = stack[0].m_obj;
lean_object* v_a_2753_ = stack[1].m_obj;
lean_object* v_a_2754_ = stack[2].m_obj;
lean_object* v_a_2755_ = stack[3].m_obj;
lean_object* v_a_2756_ = stack[4].m_obj;
lean_object* v_a_2757_ = stack[5].m_obj;
lean_object* v_a_2758_ = stack[6].m_obj;
lean_object* v_a_2759_ = stack[7].m_obj;
lean_object* v_a_2760_ = stack[8].m_obj;
lean_object* v_a_2761_ = stack[9].m_obj;
lean_object* v_res_2810_;
v_res_2810_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp(v_f_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_);
stack->m_obj
 = v_res_2810_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___boxed(lean_object* v_f_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp(v_f_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
lean_dec(v_a_2814_);
lean_dec_ref(v_a_2813_);
return v_res_2822_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(lean_object* v_x_2823_, uint8_t v_bi_2824_, lean_object* v_t_2825_, lean_object* v_b_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v___y_2835_; lean_object* v___x_2838_; uint8_t v_debug_2839_; 
v___x_2838_ = lean_st_ref_get(v___y_2828_);
v_debug_2839_ = lean_ctor_get_uint8(v___x_2838_, sizeof(void*)*12);
lean_dec(v___x_2838_);
if (v_debug_2839_ == 0)
{
v___y_2835_ = v___y_2828_;
goto v___jp_2834_;
}
else
{
lean_object* v___x_2840_; 
v___x_2840_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2825_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v___x_2841_; 
lean_dec_ref_known(v___x_2840_, 1);
v___x_2841_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_dec_ref_known(v___x_2841_, 1);
v___y_2835_ = v___y_2828_;
goto v___jp_2834_;
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_dec_ref(v_b_2826_);
lean_dec_ref(v_t_2825_);
lean_dec(v_x_2823_);
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
lean_dec_ref(v_b_2826_);
lean_dec_ref(v_t_2825_);
lean_dec(v_x_2823_);
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
v___jp_2834_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = l_Lean_Expr_lam___override(v_x_2823_, v_t_2825_, v_b_2826_, v_bi_2824_);
v___x_2837_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2836_, v___y_2835_);
return v___x_2837_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2823_ = stack[0].m_obj;
uint8_t v_bi_2824_ = stack[1].m_num;
lean_object* v_t_2825_ = stack[2].m_obj;
lean_object* v_b_2826_ = stack[3].m_obj;
lean_object* v___y_2827_ = stack[4].m_obj;
lean_object* v___y_2828_ = stack[5].m_obj;
lean_object* v___y_2829_ = stack[6].m_obj;
lean_object* v___y_2830_ = stack[7].m_obj;
lean_object* v___y_2831_ = stack[8].m_obj;
lean_object* v___y_2832_ = stack[9].m_obj;
lean_object* v_res_2858_;
v_res_2858_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(v_x_2823_, v_bi_2824_, v_t_2825_, v_b_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
stack->m_obj
 = v_res_2858_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg___boxed(lean_object* v_x_2859_, lean_object* v_bi_2860_, lean_object* v_t_2861_, lean_object* v_b_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
uint8_t v_bi_boxed_2870_; lean_object* v_res_2871_; 
v_bi_boxed_2870_ = lean_unbox(v_bi_2860_);
v_res_2871_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(v_x_2859_, v_bi_boxed_2870_, v_t_2861_, v_b_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
return v_res_2871_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(lean_object* v_x_2872_, lean_object* v_t_2873_, lean_object* v_v_2874_, lean_object* v_b_2875_, uint8_t v_nondep_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v___y_2885_; lean_object* v___x_2888_; uint8_t v_debug_2889_; 
v___x_2888_ = lean_st_ref_get(v___y_2878_);
v_debug_2889_ = lean_ctor_get_uint8(v___x_2888_, sizeof(void*)*12);
lean_dec(v___x_2888_);
if (v_debug_2889_ == 0)
{
v___y_2885_ = v___y_2878_;
goto v___jp_2884_;
}
else
{
lean_object* v___x_2890_; 
v___x_2890_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2873_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v___x_2891_; 
lean_dec_ref_known(v___x_2890_, 1);
v___x_2891_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_v_2874_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v___x_2892_; 
lean_dec_ref_known(v___x_2891_, 1);
v___x_2892_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2875_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_dec_ref_known(v___x_2892_, 1);
v___y_2885_ = v___y_2878_;
goto v___jp_2884_;
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_dec_ref(v_b_2875_);
lean_dec_ref(v_v_2874_);
lean_dec_ref(v_t_2873_);
lean_dec(v_x_2872_);
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2892_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2892_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_dec_ref(v_b_2875_);
lean_dec_ref(v_v_2874_);
lean_dec_ref(v_t_2873_);
lean_dec(v_x_2872_);
v_a_2901_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2891_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2891_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
lean_dec_ref(v_b_2875_);
lean_dec_ref(v_v_2874_);
lean_dec_ref(v_t_2873_);
lean_dec(v_x_2872_);
v_a_2909_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2890_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2890_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
v___jp_2884_:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = l_Lean_Expr_letE___override(v_x_2872_, v_t_2873_, v_v_2874_, v_b_2875_, v_nondep_2876_);
v___x_2887_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2886_, v___y_2885_);
return v___x_2887_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2872_ = stack[0].m_obj;
lean_object* v_t_2873_ = stack[1].m_obj;
lean_object* v_v_2874_ = stack[2].m_obj;
lean_object* v_b_2875_ = stack[3].m_obj;
uint8_t v_nondep_2876_ = stack[4].m_num;
lean_object* v___y_2877_ = stack[5].m_obj;
lean_object* v___y_2878_ = stack[6].m_obj;
lean_object* v___y_2879_ = stack[7].m_obj;
lean_object* v___y_2880_ = stack[8].m_obj;
lean_object* v___y_2881_ = stack[9].m_obj;
lean_object* v___y_2882_ = stack[10].m_obj;
lean_object* v_res_2917_;
v_res_2917_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_x_2872_, v_t_2873_, v_v_2874_, v_b_2875_, v_nondep_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
stack->m_obj
 = v_res_2917_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg___boxed(lean_object* v_x_2918_, lean_object* v_t_2919_, lean_object* v_v_2920_, lean_object* v_b_2921_, lean_object* v_nondep_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
uint8_t v_nondep_boxed_2930_; lean_object* v_res_2931_; 
v_nondep_boxed_2930_ = lean_unbox(v_nondep_2922_);
v_res_2931_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_x_2918_, v_t_2919_, v_v_2920_, v_b_2921_, v_nondep_boxed_2930_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
return v_res_2931_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(lean_object* v_k_2932_, lean_object* v_t_2933_){
_start:
{
if (lean_obj_tag(v_t_2933_) == 0)
{
lean_object* v_k_2934_; lean_object* v_l_2935_; lean_object* v_r_2936_; uint8_t v___x_2937_; 
v_k_2934_ = lean_ctor_get(v_t_2933_, 1);
v_l_2935_ = lean_ctor_get(v_t_2933_, 3);
v_r_2936_ = lean_ctor_get(v_t_2933_, 4);
v___x_2937_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2932_, v_k_2934_);
switch(v___x_2937_)
{
case 0:
{
v_t_2933_ = v_l_2935_;
goto _start;
}
case 1:
{
uint8_t v___x_2939_; 
v___x_2939_ = 1;
return v___x_2939_;
}
default: 
{
v_t_2933_ = v_r_2936_;
goto _start;
}
}
}
else
{
uint8_t v___x_2941_; 
v___x_2941_ = 0;
return v___x_2941_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2932_ = stack[0].m_obj;
lean_object* v_t_2933_ = stack[1].m_obj;
uint8_t v_res_2942_;
v_res_2942_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(v_k_2932_, v_t_2933_);
stack->m_num = v_res_2942_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg___boxed(lean_object* v_k_2943_, lean_object* v_t_2944_){
_start:
{
uint8_t v_res_2945_; lean_object* v_r_2946_; 
v_res_2945_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(v_k_2943_, v_t_2944_);
lean_dec(v_t_2944_);
lean_dec(v_k_2943_);
v_r_2946_ = lean_box(v_res_2945_);
return v_r_2946_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(lean_object* v_x_2947_, uint8_t v_bi_2948_, lean_object* v_t_2949_, lean_object* v_b_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v___y_2959_; lean_object* v___x_2962_; uint8_t v_debug_2963_; 
v___x_2962_ = lean_st_ref_get(v___y_2952_);
v_debug_2963_ = lean_ctor_get_uint8(v___x_2962_, sizeof(void*)*12);
lean_dec(v___x_2962_);
if (v_debug_2963_ == 0)
{
v___y_2959_ = v___y_2952_;
goto v___jp_2958_;
}
else
{
lean_object* v___x_2964_; 
v___x_2964_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2949_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v___x_2965_; 
lean_dec_ref_known(v___x_2964_, 1);
v___x_2965_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_dec_ref_known(v___x_2965_, 1);
v___y_2959_ = v___y_2952_;
goto v___jp_2958_;
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_dec_ref(v_b_2950_);
lean_dec_ref(v_t_2949_);
lean_dec(v_x_2947_);
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2965_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2965_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_dec_ref(v_b_2950_);
lean_dec_ref(v_t_2949_);
lean_dec(v_x_2947_);
v_a_2974_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2964_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2964_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
v___jp_2958_:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2960_ = l_Lean_Expr_forallE___override(v_x_2947_, v_t_2949_, v_b_2950_, v_bi_2948_);
v___x_2961_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2960_, v___y_2959_);
return v___x_2961_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2947_ = stack[0].m_obj;
uint8_t v_bi_2948_ = stack[1].m_num;
lean_object* v_t_2949_ = stack[2].m_obj;
lean_object* v_b_2950_ = stack[3].m_obj;
lean_object* v___y_2951_ = stack[4].m_obj;
lean_object* v___y_2952_ = stack[5].m_obj;
lean_object* v___y_2953_ = stack[6].m_obj;
lean_object* v___y_2954_ = stack[7].m_obj;
lean_object* v___y_2955_ = stack[8].m_obj;
lean_object* v___y_2956_ = stack[9].m_obj;
lean_object* v_res_2982_;
v_res_2982_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(v_x_2947_, v_bi_2948_, v_t_2949_, v_b_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
stack->m_obj
 = v_res_2982_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg___boxed(lean_object* v_x_2983_, lean_object* v_bi_2984_, lean_object* v_t_2985_, lean_object* v_b_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
uint8_t v_bi_boxed_2994_; lean_object* v_res_2995_; 
v_bi_boxed_2994_ = lean_unbox(v_bi_2984_);
v_res_2995_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(v_x_2983_, v_bi_boxed_2994_, v_t_2985_, v_b_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
return v_res_2995_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(lean_object* v_d_2996_, lean_object* v_e_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
lean_object* v___y_3006_; lean_object* v___x_3009_; uint8_t v_debug_3010_; 
v___x_3009_ = lean_st_ref_get(v___y_2999_);
v_debug_3010_ = lean_ctor_get_uint8(v___x_3009_, sizeof(void*)*12);
lean_dec(v___x_3009_);
if (v_debug_3010_ == 0)
{
v___y_3006_ = v___y_2999_;
goto v___jp_3005_;
}
else
{
lean_object* v___x_3011_; 
v___x_3011_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_dec_ref_known(v___x_3011_, 1);
v___y_3006_ = v___y_2999_;
goto v___jp_3005_;
}
else
{
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3019_; 
lean_dec_ref(v_e_2997_);
lean_dec(v_d_2996_);
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3014_ = v___x_3011_;
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_dec(v___x_3011_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3017_; 
if (v_isShared_3015_ == 0)
{
v___x_3017_ = v___x_3014_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_a_3012_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
}
v___jp_3005_:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = l_Lean_Expr_mdata___override(v_d_2996_, v_e_2997_);
v___x_3008_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_3007_, v___y_3006_);
return v___x_3008_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_2996_ = stack[0].m_obj;
lean_object* v_e_2997_ = stack[1].m_obj;
lean_object* v___y_2998_ = stack[2].m_obj;
lean_object* v___y_2999_ = stack[3].m_obj;
lean_object* v___y_3000_ = stack[4].m_obj;
lean_object* v___y_3001_ = stack[5].m_obj;
lean_object* v___y_3002_ = stack[6].m_obj;
lean_object* v___y_3003_ = stack[7].m_obj;
lean_object* v_res_3020_;
v_res_3020_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(v_d_2996_, v_e_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
stack->m_obj
 = v_res_3020_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg___boxed(lean_object* v_d_3021_, lean_object* v_e_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(v_d_3021_, v_e_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
return v_res_3030_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(lean_object* v_structName_3031_, lean_object* v_idx_3032_, lean_object* v_struct_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
lean_object* v___y_3042_; lean_object* v___x_3045_; uint8_t v_debug_3046_; 
v___x_3045_ = lean_st_ref_get(v___y_3035_);
v_debug_3046_ = lean_ctor_get_uint8(v___x_3045_, sizeof(void*)*12);
lean_dec(v___x_3045_);
if (v_debug_3046_ == 0)
{
v___y_3042_ = v___y_3035_;
goto v___jp_3041_;
}
else
{
lean_object* v___x_3047_; 
v___x_3047_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_struct_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_dec_ref_known(v___x_3047_, 1);
v___y_3042_ = v___y_3035_;
goto v___jp_3041_;
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_dec_ref(v_struct_3033_);
lean_dec(v_idx_3032_);
lean_dec(v_structName_3031_);
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_3047_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3047_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
v___jp_3041_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = l_Lean_Expr_proj___override(v_structName_3031_, v_idx_3032_, v_struct_3033_);
v___x_3044_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_3043_, v___y_3042_);
return v___x_3044_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_structName_3031_ = stack[0].m_obj;
lean_object* v_idx_3032_ = stack[1].m_obj;
lean_object* v_struct_3033_ = stack[2].m_obj;
lean_object* v___y_3034_ = stack[3].m_obj;
lean_object* v___y_3035_ = stack[4].m_obj;
lean_object* v___y_3036_ = stack[5].m_obj;
lean_object* v___y_3037_ = stack[6].m_obj;
lean_object* v___y_3038_ = stack[7].m_obj;
lean_object* v___y_3039_ = stack[8].m_obj;
lean_object* v_res_3056_;
v_res_3056_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(v_structName_3031_, v_idx_3032_, v_struct_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
stack->m_obj
 = v_res_3056_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg___boxed(lean_object* v_structName_3057_, lean_object* v_idx_3058_, lean_object* v_struct_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(v_structName_3057_, v_idx_3058_, v_struct_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
return v_res_3067_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(lean_object* v_f_3068_, lean_object* v_a_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v___y_3078_; lean_object* v___x_3081_; uint8_t v_debug_3082_; 
v___x_3081_ = lean_st_ref_get(v___y_3071_);
v_debug_3082_ = lean_ctor_get_uint8(v___x_3081_, sizeof(void*)*12);
lean_dec(v___x_3081_);
if (v_debug_3082_ == 0)
{
v___y_3078_ = v___y_3071_;
goto v___jp_3077_;
}
else
{
lean_object* v___x_3083_; 
v___x_3083_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_3068_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v___x_3084_; 
lean_dec_ref_known(v___x_3083_, 1);
v___x_3084_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_dec_ref_known(v___x_3084_, 1);
v___y_3078_ = v___y_3071_;
goto v___jp_3077_;
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec_ref(v_a_3069_);
lean_dec_ref(v_f_3068_);
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_dec_ref(v_a_3069_);
lean_dec_ref(v_f_3068_);
v_a_3093_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3083_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3083_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
v___jp_3077_:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = l_Lean_Expr_app___override(v_f_3068_, v_a_3069_);
v___x_3080_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_3079_, v___y_3078_);
return v___x_3080_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3068_ = stack[0].m_obj;
lean_object* v_a_3069_ = stack[1].m_obj;
lean_object* v___y_3070_ = stack[2].m_obj;
lean_object* v___y_3071_ = stack[3].m_obj;
lean_object* v___y_3072_ = stack[4].m_obj;
lean_object* v___y_3073_ = stack[5].m_obj;
lean_object* v___y_3074_ = stack[6].m_obj;
lean_object* v___y_3075_ = stack[7].m_obj;
lean_object* v_res_3101_;
v_res_3101_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(v_f_3068_, v_a_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
stack->m_obj
 = v_res_3101_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg___boxed(lean_object* v_f_3102_, lean_object* v_a_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(v_f_3102_, v_a_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
return v_res_3111_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(lean_object* v_a_3112_, lean_object* v_visited_3113_, lean_object* v_types_3114_, lean_object* v_subst_3115_, lean_object* v_a_x3f_3116_){
_start:
{
lean_object* v___x_3118_; lean_object* v_visitedClosed_3119_; lean_object* v_hasDepLetCache_3120_; lean_object* v_numConverted_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3131_; 
v___x_3118_ = lean_st_ref_take(v_a_3112_);
v_visitedClosed_3119_ = lean_ctor_get(v___x_3118_, 3);
v_hasDepLetCache_3120_ = lean_ctor_get(v___x_3118_, 4);
v_numConverted_3121_ = lean_ctor_get(v___x_3118_, 5);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3131_ == 0)
{
lean_object* v_unused_3132_; lean_object* v_unused_3133_; lean_object* v_unused_3134_; 
v_unused_3132_ = lean_ctor_get(v___x_3118_, 2);
lean_dec(v_unused_3132_);
v_unused_3133_ = lean_ctor_get(v___x_3118_, 1);
lean_dec(v_unused_3133_);
v_unused_3134_ = lean_ctor_get(v___x_3118_, 0);
lean_dec(v_unused_3134_);
v___x_3123_ = v___x_3118_;
v_isShared_3124_ = v_isSharedCheck_3131_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_numConverted_3121_);
lean_inc(v_hasDepLetCache_3120_);
lean_inc(v_visitedClosed_3119_);
lean_dec(v___x_3118_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3131_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3125_; lean_object* v___x_3127_; 
v___x_3125_ = lean_box(0);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 2, v_subst_3115_);
lean_ctor_set(v___x_3123_, 1, v_types_3114_);
lean_ctor_set(v___x_3123_, 0, v_visited_3113_);
v___x_3127_ = v___x_3123_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_visited_3113_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v_types_3114_);
lean_ctor_set(v_reuseFailAlloc_3130_, 2, v_subst_3115_);
lean_ctor_set(v_reuseFailAlloc_3130_, 3, v_visitedClosed_3119_);
lean_ctor_set(v_reuseFailAlloc_3130_, 4, v_hasDepLetCache_3120_);
lean_ctor_set(v_reuseFailAlloc_3130_, 5, v_numConverted_3121_);
v___x_3127_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = lean_st_ref_put(v_a_3112_, v___x_3127_);
v___x_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3125_);
return v___x_3129_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3112_ = stack[0].m_obj;
lean_object* v_visited_3113_ = stack[1].m_obj;
lean_object* v_types_3114_ = stack[2].m_obj;
lean_object* v_subst_3115_ = stack[3].m_obj;
lean_object* v_a_x3f_3116_ = stack[4].m_obj;
lean_object* v_res_3135_;
v_res_3135_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(v_a_3112_, v_visited_3113_, v_types_3114_, v_subst_3115_, v_a_x3f_3116_);
stack->m_obj
 = v_res_3135_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0___boxed(lean_object* v_a_3136_, lean_object* v_visited_3137_, lean_object* v_types_3138_, lean_object* v_subst_3139_, lean_object* v_a_x3f_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(v_a_3136_, v_visited_3137_, v_types_3138_, v_subst_3139_, v_a_x3f_3140_);
lean_dec(v_a_x3f_3140_);
lean_dec(v_a_3136_);
return v_res_3142_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0(void){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3143_ = lean_unsigned_to_nat(32u);
v___x_3144_ = lean_mk_empty_array_with_capacity(v___x_3143_);
v___x_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3144_);
return v___x_3145_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1(void){
_start:
{
size_t v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3146_ = ((size_t)5ULL);
v___x_3147_ = lean_unsigned_to_nat(0u);
v___x_3148_ = lean_unsigned_to_nat(32u);
v___x_3149_ = lean_mk_empty_array_with_capacity(v___x_3148_);
v___x_3150_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0);
v___x_3151_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
lean_ctor_set(v___x_3151_, 1, v___x_3149_);
lean_ctor_set(v___x_3151_, 2, v___x_3147_);
lean_ctor_set(v___x_3151_, 3, v___x_3147_);
lean_ctor_set_usize(v___x_3151_, 4, v___x_3146_);
return v___x_3151_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2(void){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3152_ = lean_unsigned_to_nat(0u);
v___x_3153_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1);
v___x_3154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
lean_ctor_set(v___x_3154_, 1, v___x_3152_);
lean_ctor_set(v___x_3154_, 2, v___x_3152_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0___boxed(lean_object* v_body_3155_, lean_object* v_binderType_3156_, lean_object* v_a_3157_, lean_object* v_binderName_3158_, lean_object* v_binderInfo_3159_, lean_object* v_e_3160_, lean_object* v_x_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
uint8_t v_binderInfo_75570__boxed_3171_; lean_object* v_res_3172_; 
v_binderInfo_75570__boxed_3171_ = lean_unbox(v_binderInfo_3159_);
v_res_3172_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0(v_body_3155_, v_binderType_3156_, v_a_3157_, v_binderName_3158_, v_binderInfo_75570__boxed_3171_, v_e_3160_, v_x_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec_ref(v_x_3161_);
lean_dec_ref(v_binderType_3156_);
return v_res_3172_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0(lean_object* v_body_3173_, lean_object* v_binderType_3174_, lean_object* v_a_3175_, lean_object* v_binderName_3176_, uint8_t v_binderInfo_3177_, lean_object* v_e_3178_, lean_object* v_x_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v___x_3189_; 
lean_inc_ref(v_body_3173_);
v___x_3189_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(v_body_3173_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3205_; 
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3192_ = v___x_3189_;
v_isShared_3193_ = v_isSharedCheck_3205_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3189_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3205_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
size_t v___x_3194_; size_t v___x_3195_; uint8_t v___x_3196_; 
v___x_3194_ = lean_ptr_addr(v_binderType_3174_);
v___x_3195_ = lean_ptr_addr(v_a_3175_);
v___x_3196_ = lean_usize_dec_eq(v___x_3194_, v___x_3195_);
if (v___x_3196_ == 0)
{
lean_object* v___x_3197_; 
lean_del_object(v___x_3192_);
lean_dec_ref(v_e_3178_);
lean_dec_ref(v_body_3173_);
v___x_3197_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(v_binderName_3176_, v_binderInfo_3177_, v_a_3175_, v_a_3190_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
return v___x_3197_;
}
else
{
size_t v___x_3198_; size_t v___x_3199_; uint8_t v___x_3200_; 
v___x_3198_ = lean_ptr_addr(v_body_3173_);
lean_dec_ref(v_body_3173_);
v___x_3199_ = lean_ptr_addr(v_a_3190_);
v___x_3200_ = lean_usize_dec_eq(v___x_3198_, v___x_3199_);
if (v___x_3200_ == 0)
{
lean_object* v___x_3201_; 
lean_del_object(v___x_3192_);
lean_dec_ref(v_e_3178_);
v___x_3201_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(v_binderName_3176_, v_binderInfo_3177_, v_a_3175_, v_a_3190_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
return v___x_3201_;
}
else
{
lean_object* v___x_3203_; 
lean_dec(v_a_3190_);
lean_dec(v_binderName_3176_);
lean_dec_ref(v_a_3175_);
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 0, v_e_3178_);
v___x_3203_ = v___x_3192_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_e_3178_);
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
}
else
{
lean_dec_ref(v_e_3178_);
lean_dec(v_binderName_3176_);
lean_dec_ref(v_a_3175_);
lean_dec_ref(v_body_3173_);
return v___x_3189_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_3173_ = stack[0].m_obj;
lean_object* v_binderType_3174_ = stack[1].m_obj;
lean_object* v_a_3175_ = stack[2].m_obj;
lean_object* v_binderName_3176_ = stack[3].m_obj;
uint8_t v_binderInfo_3177_ = stack[4].m_num;
lean_object* v_e_3178_ = stack[5].m_obj;
lean_object* v_x_3179_ = stack[6].m_obj;
lean_object* v___y_3180_ = stack[7].m_obj;
lean_object* v___y_3181_ = stack[8].m_obj;
lean_object* v___y_3182_ = stack[9].m_obj;
lean_object* v___y_3183_ = stack[10].m_obj;
lean_object* v___y_3184_ = stack[11].m_obj;
lean_object* v___y_3185_ = stack[12].m_obj;
lean_object* v___y_3186_ = stack[13].m_obj;
lean_object* v___y_3187_ = stack[14].m_obj;
lean_object* v_res_3206_;
v_res_3206_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0(v_body_3173_, v_binderType_3174_, v_a_3175_, v_binderName_3176_, v_binderInfo_3177_, v_e_3178_, v_x_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
stack->m_obj
 = v_res_3206_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0___boxed(lean_object* v_body_3207_, lean_object* v_binderType_3208_, lean_object* v_a_3209_, lean_object* v_binderName_3210_, lean_object* v_binderInfo_3211_, lean_object* v_e_3212_, lean_object* v_x_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
uint8_t v_binderInfo_75597__boxed_3223_; lean_object* v_res_3224_; 
v_binderInfo_75597__boxed_3223_ = lean_unbox(v_binderInfo_3211_);
v_res_3224_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0(v_body_3207_, v_binderType_3208_, v_a_3209_, v_binderName_3210_, v_binderInfo_75597__boxed_3223_, v_e_3212_, v_x_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec_ref(v_x_3213_);
lean_dec_ref(v_binderType_3208_);
return v_res_3224_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(lean_object* v_e_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_){
_start:
{
if (lean_obj_tag(v_e_3225_) == 7)
{
lean_object* v_binderName_3235_; lean_object* v_binderType_3236_; lean_object* v_body_3237_; uint8_t v_binderInfo_3238_; lean_object* v___x_3239_; 
v_binderName_3235_ = lean_ctor_get(v_e_3225_, 0);
lean_inc(v_binderName_3235_);
v_binderType_3236_ = lean_ctor_get(v_e_3225_, 1);
lean_inc_ref_n(v_binderType_3236_, 2);
v_body_3237_ = lean_ctor_get(v_e_3225_, 2);
lean_inc_ref(v_body_3237_);
v_binderInfo_3238_ = lean_ctor_get_uint8(v_e_3225_, sizeof(void*)*3 + 8);
v___x_3239_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_binderType_3236_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3241_; lean_object* v___f_3242_; lean_object* v___x_3243_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc_n(v_a_3240_, 2);
lean_dec_ref_known(v___x_3239_, 1);
v___x_3241_ = lean_box(v_binderInfo_3238_);
lean_inc(v_binderName_3235_);
lean_inc_ref(v_binderType_3236_);
v___f_3242_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0___boxed), 16, 6);
lean_closure_set(v___f_3242_, 0, v_body_3237_);
lean_closure_set(v___f_3242_, 1, v_binderType_3236_);
lean_closure_set(v___f_3242_, 2, v_a_3240_);
lean_closure_set(v___f_3242_, 3, v_binderName_3235_);
lean_closure_set(v___f_3242_, 4, v___x_3241_);
lean_closure_set(v___f_3242_, 5, v_e_3225_);
v___x_3243_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3240_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_object* v_a_3244_; lean_object* v___x_3245_; 
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
lean_inc_n(v_a_3244_, 2);
lean_dec_ref_known(v___x_3243_, 1);
v___x_3245_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_binderType_3236_, v_a_3244_, v_a_3226_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v_cleanSuffix_3246_; lean_object* v___x_3247_; uint8_t v___y_3249_; lean_object* v___x_3252_; uint8_t v___x_3253_; 
lean_dec_ref_known(v___x_3245_, 1);
v_cleanSuffix_3246_ = lean_ctor_get(v_a_3226_, 2);
v___x_3247_ = lean_box(0);
v___x_3252_ = l_Lean_Expr_looseBVarRange(v_binderType_3236_);
lean_dec_ref(v_binderType_3236_);
v___x_3253_ = lean_nat_dec_le(v___x_3252_, v_cleanSuffix_3246_);
lean_dec(v___x_3252_);
if (v___x_3253_ == 0)
{
uint8_t v___x_3254_; 
v___x_3254_ = 1;
v___y_3249_ = v___x_3254_;
goto v___jp_3248_;
}
else
{
uint8_t v___x_3255_; 
v___x_3255_ = 0;
v___y_3249_ = v___x_3255_;
goto v___jp_3248_;
}
v___jp_3248_:
{
uint8_t v___x_3250_; lean_object* v___x_3251_; 
v___x_3250_ = 0;
v___x_3251_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_binderName_3235_, v_a_3244_, v___x_3247_, v___y_3249_, v___x_3250_, v___f_3242_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_);
return v___x_3251_;
}
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
lean_dec(v_a_3244_);
lean_dec_ref(v___f_3242_);
lean_dec_ref(v_binderType_3236_);
lean_dec(v_binderName_3235_);
v_a_3256_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v___x_3245_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3245_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3261_; 
if (v_isShared_3259_ == 0)
{
v___x_3261_ = v___x_3258_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
else
{
lean_dec_ref(v___f_3242_);
lean_dec_ref(v_binderType_3236_);
lean_dec(v_binderName_3235_);
return v___x_3243_;
}
}
else
{
lean_dec_ref(v_body_3237_);
lean_dec_ref(v_binderType_3236_);
lean_dec(v_binderName_3235_);
lean_dec_ref_known(v_e_3225_, 3);
return v___x_3239_;
}
}
else
{
lean_object* v___x_3264_; 
lean_inc_ref(v_e_3225_);
v___x_3264_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_e_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_object* v_a_3265_; lean_object* v_numCandidates_3266_; lean_object* v_cleanSuffix_3267_; lean_object* v___x_3268_; uint8_t v___x_3269_; 
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
v_numCandidates_3266_ = lean_ctor_get(v_a_3226_, 1);
v_cleanSuffix_3267_ = lean_ctor_get(v_a_3226_, 2);
v___x_3268_ = lean_unsigned_to_nat(0u);
v___x_3269_ = lean_nat_dec_lt(v___x_3268_, v_numCandidates_3266_);
if (v___x_3269_ == 0)
{
lean_dec_ref(v_e_3225_);
return v___x_3264_;
}
else
{
lean_object* v___x_3270_; uint8_t v___x_3271_; 
v___x_3270_ = l_Lean_Expr_looseBVarRange(v_e_3225_);
lean_dec_ref(v_e_3225_);
v___x_3271_ = lean_nat_dec_le(v___x_3270_, v_cleanSuffix_3267_);
lean_dec(v___x_3270_);
if (v___x_3271_ == 0)
{
lean_object* v___x_3272_; 
lean_inc_n(v_a_3265_, 2);
lean_dec_ref_known(v___x_3264_, 1);
v___x_3272_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3265_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v_a_3273_; lean_object* v___x_3274_; 
v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
lean_inc(v_a_3273_);
lean_dec_ref_known(v___x_3272_, 1);
v___x_3274_ = l_Lean_Meta_getLevel(v_a_3273_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3281_ == 0)
{
lean_object* v_unused_3282_; 
v_unused_3282_ = lean_ctor_get(v___x_3274_, 0);
lean_dec(v_unused_3282_);
v___x_3276_ = v___x_3274_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_dec(v___x_3274_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 0, v_a_3265_);
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3265_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec(v_a_3265_);
v_a_3283_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3274_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3274_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
else
{
lean_dec(v_a_3265_);
return v___x_3272_;
}
}
else
{
return v___x_3264_;
}
}
}
else
{
lean_dec_ref(v_e_3225_);
return v___x_3264_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3225_ = stack[0].m_obj;
lean_object* v_a_3226_ = stack[1].m_obj;
lean_object* v_a_3227_ = stack[2].m_obj;
lean_object* v_a_3228_ = stack[3].m_obj;
lean_object* v_a_3229_ = stack[4].m_obj;
lean_object* v_a_3230_ = stack[5].m_obj;
lean_object* v_a_3231_ = stack[6].m_obj;
lean_object* v_a_3232_ = stack[7].m_obj;
lean_object* v_a_3233_ = stack[8].m_obj;
lean_object* v_res_3291_;
v_res_3291_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(v_e_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_);
stack->m_obj
 = v_res_3291_;
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1(lean_object* v_body_3292_, lean_object* v_type_3293_, lean_object* v_a_3294_, lean_object* v_declName_3295_, lean_object* v_a_3296_, uint8_t v_nondep_3297_, lean_object* v_value_3298_, lean_object* v_e_3299_, uint8_t v___y_3300_, lean_object* v_x_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v___x_3311_; 
lean_inc_ref(v_body_3292_);
v___x_3311_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_body_3292_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3378_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3314_ = v___x_3311_;
v_isShared_3315_ = v_isSharedCheck_3378_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3311_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3378_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; uint8_t v_nondep_x27_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___x_3348_; 
v___x_3348_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v___y_3307_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; uint8_t v___x_3350_; 
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_a_3349_);
lean_dec_ref_known(v___x_3348_, 1);
v___x_3350_ = 1;
if (v_nondep_3297_ == 0)
{
if (v___y_3300_ == 0)
{
lean_dec(v_a_3349_);
v_nondep_x27_3339_ = v_nondep_3297_;
v___y_3340_ = v___y_3304_;
v___y_3341_ = v___y_3305_;
v___y_3342_ = v___y_3306_;
v___y_3343_ = v___y_3307_;
v___y_3344_ = v___y_3308_;
v___y_3345_ = v___y_3309_;
goto v___jp_3338_;
}
else
{
lean_object* v___x_3351_; uint8_t v___x_3352_; 
v___x_3351_ = l_Lean_Expr_fvarId_x21(v_x_3301_);
v___x_3352_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(v___x_3351_, v_a_3349_);
lean_dec(v_a_3349_);
lean_dec(v___x_3351_);
if (v___x_3352_ == 0)
{
lean_object* v___x_3353_; lean_object* v_visited_3354_; lean_object* v_types_3355_; lean_object* v_subst_3356_; lean_object* v_visitedClosed_3357_; lean_object* v_hasDepLetCache_3358_; lean_object* v_numConverted_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3369_; 
v___x_3353_ = lean_st_ref_take(v___y_3303_);
v_visited_3354_ = lean_ctor_get(v___x_3353_, 0);
v_types_3355_ = lean_ctor_get(v___x_3353_, 1);
v_subst_3356_ = lean_ctor_get(v___x_3353_, 2);
v_visitedClosed_3357_ = lean_ctor_get(v___x_3353_, 3);
v_hasDepLetCache_3358_ = lean_ctor_get(v___x_3353_, 4);
v_numConverted_3359_ = lean_ctor_get(v___x_3353_, 5);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3361_ = v___x_3353_;
v_isShared_3362_ = v_isSharedCheck_3369_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_numConverted_3359_);
lean_inc(v_hasDepLetCache_3358_);
lean_inc(v_visitedClosed_3357_);
lean_inc(v_subst_3356_);
lean_inc(v_types_3355_);
lean_inc(v_visited_3354_);
lean_dec(v___x_3353_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3369_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3366_; 
v___x_3363_ = lean_unsigned_to_nat(1u);
v___x_3364_ = lean_nat_add(v_numConverted_3359_, v___x_3363_);
lean_dec(v_numConverted_3359_);
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 5, v___x_3364_);
v___x_3366_ = v___x_3361_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_visited_3354_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_types_3355_);
lean_ctor_set(v_reuseFailAlloc_3368_, 2, v_subst_3356_);
lean_ctor_set(v_reuseFailAlloc_3368_, 3, v_visitedClosed_3357_);
lean_ctor_set(v_reuseFailAlloc_3368_, 4, v_hasDepLetCache_3358_);
lean_ctor_set(v_reuseFailAlloc_3368_, 5, v___x_3364_);
v___x_3366_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v___x_3367_; 
v___x_3367_ = lean_st_ref_put(v___y_3303_, v___x_3366_);
v_nondep_x27_3339_ = v___x_3350_;
v___y_3340_ = v___y_3304_;
v___y_3341_ = v___y_3305_;
v___y_3342_ = v___y_3306_;
v___y_3343_ = v___y_3307_;
v___y_3344_ = v___y_3308_;
v___y_3345_ = v___y_3309_;
goto v___jp_3338_;
}
}
}
else
{
v_nondep_x27_3339_ = v_nondep_3297_;
v___y_3340_ = v___y_3304_;
v___y_3341_ = v___y_3305_;
v___y_3342_ = v___y_3306_;
v___y_3343_ = v___y_3307_;
v___y_3344_ = v___y_3308_;
v___y_3345_ = v___y_3309_;
goto v___jp_3338_;
}
}
}
else
{
lean_dec(v_a_3349_);
v_nondep_x27_3339_ = v___x_3350_;
v___y_3340_ = v___y_3304_;
v___y_3341_ = v___y_3305_;
v___y_3342_ = v___y_3306_;
v___y_3343_ = v___y_3307_;
v___y_3344_ = v___y_3308_;
v___y_3345_ = v___y_3309_;
goto v___jp_3338_;
}
}
else
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3377_; 
lean_del_object(v___x_3314_);
lean_dec(v_a_3312_);
lean_dec_ref(v_e_3299_);
lean_dec_ref(v_a_3296_);
lean_dec(v_declName_3295_);
lean_dec_ref(v_a_3294_);
lean_dec_ref(v_body_3292_);
v_a_3370_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3372_ = v___x_3348_;
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3348_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3375_; 
if (v_isShared_3373_ == 0)
{
v___x_3375_ = v___x_3372_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_a_3370_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
v___jp_3316_:
{
size_t v___x_3323_; size_t v___x_3324_; uint8_t v___x_3325_; 
v___x_3323_ = lean_ptr_addr(v_type_3293_);
v___x_3324_ = lean_ptr_addr(v_a_3294_);
v___x_3325_ = lean_usize_dec_eq(v___x_3323_, v___x_3324_);
if (v___x_3325_ == 0)
{
lean_object* v___x_3326_; 
lean_del_object(v___x_3314_);
lean_dec_ref(v_e_3299_);
lean_dec_ref(v_body_3292_);
v___x_3326_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3295_, v_a_3294_, v_a_3296_, v_a_3312_, v_nondep_3297_, v___y_3321_, v___y_3319_, v___y_3322_, v___y_3317_, v___y_3320_, v___y_3318_);
return v___x_3326_;
}
else
{
size_t v___x_3327_; size_t v___x_3328_; uint8_t v___x_3329_; 
v___x_3327_ = lean_ptr_addr(v_value_3298_);
v___x_3328_ = lean_ptr_addr(v_a_3296_);
v___x_3329_ = lean_usize_dec_eq(v___x_3327_, v___x_3328_);
if (v___x_3329_ == 0)
{
lean_object* v___x_3330_; 
lean_del_object(v___x_3314_);
lean_dec_ref(v_e_3299_);
lean_dec_ref(v_body_3292_);
v___x_3330_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3295_, v_a_3294_, v_a_3296_, v_a_3312_, v_nondep_3297_, v___y_3321_, v___y_3319_, v___y_3322_, v___y_3317_, v___y_3320_, v___y_3318_);
return v___x_3330_;
}
else
{
size_t v___x_3331_; size_t v___x_3332_; uint8_t v___x_3333_; 
v___x_3331_ = lean_ptr_addr(v_body_3292_);
lean_dec_ref(v_body_3292_);
v___x_3332_ = lean_ptr_addr(v_a_3312_);
v___x_3333_ = lean_usize_dec_eq(v___x_3331_, v___x_3332_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; 
lean_del_object(v___x_3314_);
lean_dec_ref(v_e_3299_);
v___x_3334_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3295_, v_a_3294_, v_a_3296_, v_a_3312_, v_nondep_3297_, v___y_3321_, v___y_3319_, v___y_3322_, v___y_3317_, v___y_3320_, v___y_3318_);
return v___x_3334_;
}
else
{
lean_object* v___x_3336_; 
lean_dec(v_a_3312_);
lean_dec_ref(v_a_3296_);
lean_dec(v_declName_3295_);
lean_dec_ref(v_a_3294_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 0, v_e_3299_);
v___x_3336_ = v___x_3314_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_e_3299_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
}
v___jp_3338_:
{
if (v_nondep_3297_ == 0)
{
if (v_nondep_x27_3339_ == 0)
{
v___y_3317_ = v___y_3343_;
v___y_3318_ = v___y_3345_;
v___y_3319_ = v___y_3341_;
v___y_3320_ = v___y_3344_;
v___y_3321_ = v___y_3340_;
v___y_3322_ = v___y_3342_;
goto v___jp_3316_;
}
else
{
lean_object* v___x_3346_; 
lean_del_object(v___x_3314_);
lean_dec_ref(v_e_3299_);
lean_dec_ref(v_body_3292_);
v___x_3346_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3295_, v_a_3294_, v_a_3296_, v_a_3312_, v_nondep_x27_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
return v___x_3346_;
}
}
else
{
if (v_nondep_x27_3339_ == 0)
{
lean_object* v___x_3347_; 
lean_del_object(v___x_3314_);
lean_dec_ref(v_e_3299_);
lean_dec_ref(v_body_3292_);
v___x_3347_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3295_, v_a_3294_, v_a_3296_, v_a_3312_, v_nondep_x27_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
return v___x_3347_;
}
else
{
v___y_3317_ = v___y_3343_;
v___y_3318_ = v___y_3345_;
v___y_3319_ = v___y_3341_;
v___y_3320_ = v___y_3344_;
v___y_3321_ = v___y_3340_;
v___y_3322_ = v___y_3342_;
goto v___jp_3316_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3299_);
lean_dec_ref(v_a_3296_);
lean_dec(v_declName_3295_);
lean_dec_ref(v_a_3294_);
lean_dec_ref(v_body_3292_);
return v___x_3311_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_3292_ = stack[0].m_obj;
lean_object* v_type_3293_ = stack[1].m_obj;
lean_object* v_a_3294_ = stack[2].m_obj;
lean_object* v_declName_3295_ = stack[3].m_obj;
lean_object* v_a_3296_ = stack[4].m_obj;
uint8_t v_nondep_3297_ = stack[5].m_num;
lean_object* v_value_3298_ = stack[6].m_obj;
lean_object* v_e_3299_ = stack[7].m_obj;
uint8_t v___y_3300_ = stack[8].m_num;
lean_object* v_x_3301_ = stack[9].m_obj;
lean_object* v___y_3302_ = stack[10].m_obj;
lean_object* v___y_3303_ = stack[11].m_obj;
lean_object* v___y_3304_ = stack[12].m_obj;
lean_object* v___y_3305_ = stack[13].m_obj;
lean_object* v___y_3306_ = stack[14].m_obj;
lean_object* v___y_3307_ = stack[15].m_obj;
lean_object* v___y_3308_ = stack[16].m_obj;
lean_object* v___y_3309_ = stack[17].m_obj;
lean_object* v_res_3379_;
v_res_3379_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1(v_body_3292_, v_type_3293_, v_a_3294_, v_declName_3295_, v_a_3296_, v_nondep_3297_, v_value_3298_, v_e_3299_, v___y_3300_, v_x_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
stack->m_obj
 = v_res_3379_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1___boxed(lean_object** _args){
lean_object* v_body_3380_ = _args[0];
lean_object* v_type_3381_ = _args[1];
lean_object* v_a_3382_ = _args[2];
lean_object* v_declName_3383_ = _args[3];
lean_object* v_a_3384_ = _args[4];
lean_object* v_nondep_3385_ = _args[5];
lean_object* v_value_3386_ = _args[6];
lean_object* v_e_3387_ = _args[7];
lean_object* v___y_3388_ = _args[8];
lean_object* v_x_3389_ = _args[9];
lean_object* v___y_3390_ = _args[10];
lean_object* v___y_3391_ = _args[11];
lean_object* v___y_3392_ = _args[12];
lean_object* v___y_3393_ = _args[13];
lean_object* v___y_3394_ = _args[14];
lean_object* v___y_3395_ = _args[15];
lean_object* v___y_3396_ = _args[16];
lean_object* v___y_3397_ = _args[17];
lean_object* v___y_3398_ = _args[18];
_start:
{
uint8_t v_nondep_75753__boxed_3399_; uint8_t v___y_75755__boxed_3400_; lean_object* v_res_3401_; 
v_nondep_75753__boxed_3399_ = lean_unbox(v_nondep_3385_);
v___y_75755__boxed_3400_ = lean_unbox(v___y_3388_);
v_res_3401_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1(v_body_3380_, v_type_3381_, v_a_3382_, v_declName_3383_, v_a_3384_, v_nondep_75753__boxed_3399_, v_value_3386_, v_e_3387_, v___y_75755__boxed_3400_, v_x_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec_ref(v_x_3389_);
lean_dec_ref(v_value_3386_);
lean_dec_ref(v_type_3381_);
return v_res_3401_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3403_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_3404_ = lean_unsigned_to_nat(9u);
v___x_3405_ = lean_unsigned_to_nat(263u);
v___x_3406_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__0));
v___x_3407_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0));
v___x_3408_ = l_mkPanicMessageWithDecl(v___x_3407_, v___x_3406_, v___x_3405_, v___x_3404_, v___x_3403_);
return v___x_3408_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(lean_object* v_e_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_){
_start:
{
switch(lean_obj_tag(v_e_3409_))
{
case 5:
{
lean_object* v_fn_3419_; lean_object* v_arg_3420_; lean_object* v___y_3422_; lean_object* v_a_3423_; lean_object* v___y_3445_; lean_object* v___x_3447_; 
v_fn_3419_ = lean_ctor_get(v_e_3409_, 0);
lean_inc_ref_n(v_fn_3419_, 2);
v_arg_3420_ = lean_ctor_get(v_e_3409_, 1);
lean_inc_ref(v_arg_3420_);
v___x_3447_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_fn_3419_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; lean_object* v___x_3449_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_a_3448_);
lean_dec_ref_known(v___x_3447_, 1);
lean_inc_ref(v_arg_3420_);
v___x_3449_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_arg_3420_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3465_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3452_ = v___x_3449_;
v_isShared_3453_ = v_isSharedCheck_3465_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3449_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3465_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
size_t v___x_3454_; size_t v___x_3455_; uint8_t v___x_3456_; 
v___x_3454_ = lean_ptr_addr(v_fn_3419_);
v___x_3455_ = lean_ptr_addr(v_a_3448_);
v___x_3456_ = lean_usize_dec_eq(v___x_3454_, v___x_3455_);
if (v___x_3456_ == 0)
{
lean_object* v___x_3457_; 
lean_del_object(v___x_3452_);
lean_dec_ref_known(v_e_3409_, 2);
v___x_3457_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(v_a_3448_, v_a_3450_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
v___y_3445_ = v___x_3457_;
goto v___jp_3444_;
}
else
{
size_t v___x_3458_; size_t v___x_3459_; uint8_t v___x_3460_; 
v___x_3458_ = lean_ptr_addr(v_arg_3420_);
v___x_3459_ = lean_ptr_addr(v_a_3450_);
v___x_3460_ = lean_usize_dec_eq(v___x_3458_, v___x_3459_);
if (v___x_3460_ == 0)
{
lean_object* v___x_3461_; 
lean_del_object(v___x_3452_);
lean_dec_ref_known(v_e_3409_, 2);
v___x_3461_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(v_a_3448_, v_a_3450_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
v___y_3445_ = v___x_3461_;
goto v___jp_3444_;
}
else
{
lean_object* v___x_3463_; 
lean_dec(v_a_3450_);
lean_dec(v_a_3448_);
lean_inc_ref(v_e_3409_);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v_e_3409_);
v___x_3463_ = v___x_3452_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_e_3409_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
v___y_3422_ = v___x_3463_;
v_a_3423_ = v_e_3409_;
goto v___jp_3421_;
}
}
}
}
}
else
{
lean_dec(v_a_3448_);
lean_dec_ref(v_arg_3420_);
lean_dec_ref_known(v_e_3409_, 2);
lean_dec_ref(v_fn_3419_);
return v___x_3449_;
}
}
else
{
lean_dec_ref(v_arg_3420_);
lean_dec_ref_known(v_e_3409_, 2);
lean_dec_ref(v_fn_3419_);
return v___x_3447_;
}
v___jp_3421_:
{
lean_object* v_numCandidates_3424_; lean_object* v___x_3425_; uint8_t v___x_3426_; 
v_numCandidates_3424_ = lean_ctor_get(v_a_3410_, 1);
v___x_3425_ = lean_unsigned_to_nat(0u);
v___x_3426_ = lean_nat_dec_lt(v___x_3425_, v_numCandidates_3424_);
if (v___x_3426_ == 0)
{
lean_dec_ref(v_a_3423_);
lean_dec_ref(v_arg_3420_);
lean_dec_ref(v_fn_3419_);
return v___y_3422_;
}
else
{
lean_object* v___x_3427_; 
lean_dec_ref(v___y_3422_);
v___x_3427_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp(v_fn_3419_, v_arg_3420_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3434_ == 0)
{
lean_object* v_unused_3435_; 
v_unused_3435_ = lean_ctor_get(v___x_3427_, 0);
lean_dec(v_unused_3435_);
v___x_3429_ = v___x_3427_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_dec(v___x_3427_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v_a_3423_);
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3423_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec_ref(v_a_3423_);
v_a_3436_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3427_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3427_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
v___jp_3444_:
{
if (lean_obj_tag(v___y_3445_) == 0)
{
lean_object* v_a_3446_; 
v_a_3446_ = lean_ctor_get(v___y_3445_, 0);
lean_inc(v_a_3446_);
v___y_3422_ = v___y_3445_;
v_a_3423_ = v_a_3446_;
goto v___jp_3421_;
}
else
{
lean_dec_ref(v_arg_3420_);
lean_dec_ref(v_fn_3419_);
return v___y_3445_;
}
}
}
case 10:
{
lean_object* v_data_3466_; lean_object* v_expr_3467_; lean_object* v___x_3468_; 
v_data_3466_ = lean_ctor_get(v_e_3409_, 0);
v_expr_3467_ = lean_ctor_get(v_e_3409_, 1);
lean_inc_ref(v_expr_3467_);
v___x_3468_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_expr_3467_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3480_; 
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3471_ = v___x_3468_;
v_isShared_3472_ = v_isSharedCheck_3480_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3468_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3480_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
size_t v___x_3473_; size_t v___x_3474_; uint8_t v___x_3475_; 
v___x_3473_ = lean_ptr_addr(v_expr_3467_);
v___x_3474_ = lean_ptr_addr(v_a_3469_);
v___x_3475_ = lean_usize_dec_eq(v___x_3473_, v___x_3474_);
if (v___x_3475_ == 0)
{
lean_object* v___x_3476_; 
lean_inc(v_data_3466_);
lean_del_object(v___x_3471_);
lean_dec_ref_known(v_e_3409_, 2);
v___x_3476_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(v_data_3466_, v_a_3469_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
return v___x_3476_;
}
else
{
lean_object* v___x_3478_; 
lean_dec(v_a_3469_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v_e_3409_);
v___x_3478_ = v___x_3471_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_e_3409_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3409_, 2);
return v___x_3468_;
}
}
case 11:
{
lean_object* v_typeName_3481_; lean_object* v_idx_3482_; lean_object* v_struct_3483_; lean_object* v___y_3485_; lean_object* v_a_3486_; lean_object* v___x_3502_; 
v_typeName_3481_ = lean_ctor_get(v_e_3409_, 0);
v_idx_3482_ = lean_ctor_get(v_e_3409_, 1);
v_struct_3483_ = lean_ctor_get(v_e_3409_, 2);
lean_inc_ref(v_struct_3483_);
v___x_3502_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_struct_3483_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3515_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3505_ = v___x_3502_;
v_isShared_3506_ = v_isSharedCheck_3515_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3502_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3515_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
size_t v___x_3507_; size_t v___x_3508_; uint8_t v___x_3509_; 
v___x_3507_ = lean_ptr_addr(v_struct_3483_);
v___x_3508_ = lean_ptr_addr(v_a_3503_);
v___x_3509_ = lean_usize_dec_eq(v___x_3507_, v___x_3508_);
if (v___x_3509_ == 0)
{
lean_object* v___x_3510_; 
lean_del_object(v___x_3505_);
lean_inc(v_idx_3482_);
lean_inc(v_typeName_3481_);
v___x_3510_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(v_typeName_3481_, v_idx_3482_, v_a_3503_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; 
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_a_3511_);
v___y_3485_ = v___x_3510_;
v_a_3486_ = v_a_3511_;
goto v___jp_3484_;
}
else
{
lean_dec_ref_known(v_e_3409_, 3);
return v___x_3510_;
}
}
else
{
lean_object* v___x_3513_; 
lean_dec(v_a_3503_);
lean_inc_ref(v_e_3409_);
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 0, v_e_3409_);
v___x_3513_ = v___x_3505_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_e_3409_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
lean_inc_ref(v_e_3409_);
v___y_3485_ = v___x_3513_;
v_a_3486_ = v_e_3409_;
goto v___jp_3484_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3409_, 3);
return v___x_3502_;
}
v___jp_3484_:
{
lean_object* v_numCandidates_3487_; lean_object* v_cleanSuffix_3488_; lean_object* v___x_3489_; uint8_t v___x_3490_; 
v_numCandidates_3487_ = lean_ctor_get(v_a_3410_, 1);
v_cleanSuffix_3488_ = lean_ctor_get(v_a_3410_, 2);
v___x_3489_ = lean_unsigned_to_nat(0u);
v___x_3490_ = lean_nat_dec_lt(v___x_3489_, v_numCandidates_3487_);
if (v___x_3490_ == 0)
{
lean_dec_ref(v_a_3486_);
lean_dec_ref_known(v_e_3409_, 3);
return v___y_3485_;
}
else
{
lean_object* v___x_3491_; uint8_t v___x_3492_; 
v___x_3491_ = l_Lean_Expr_looseBVarRange(v_struct_3483_);
v___x_3492_ = lean_nat_dec_le(v___x_3491_, v_cleanSuffix_3488_);
lean_dec(v___x_3491_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3493_; 
lean_dec_ref(v___y_3485_);
v___x_3493_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(v_e_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3500_ == 0)
{
lean_object* v_unused_3501_; 
v_unused_3501_ = lean_ctor_get(v___x_3493_, 0);
lean_dec(v_unused_3501_);
v___x_3495_ = v___x_3493_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_dec(v___x_3493_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 0, v_a_3486_);
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3486_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
else
{
lean_dec_ref(v_a_3486_);
return v___x_3493_;
}
}
else
{
lean_dec_ref(v_a_3486_);
lean_dec_ref_known(v_e_3409_, 3);
return v___y_3485_;
}
}
}
}
case 6:
{
lean_object* v_binderName_3516_; lean_object* v_binderType_3517_; lean_object* v_body_3518_; uint8_t v_binderInfo_3519_; lean_object* v___x_3520_; 
v_binderName_3516_ = lean_ctor_get(v_e_3409_, 0);
lean_inc(v_binderName_3516_);
v_binderType_3517_ = lean_ctor_get(v_e_3409_, 1);
lean_inc_ref_n(v_binderType_3517_, 2);
v_body_3518_ = lean_ctor_get(v_e_3409_, 2);
lean_inc_ref(v_body_3518_);
v_binderInfo_3519_ = lean_ctor_get_uint8(v_e_3409_, sizeof(void*)*3 + 8);
v___x_3520_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_binderType_3517_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v___x_3522_; lean_object* v___f_3523_; lean_object* v___x_3524_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc_n(v_a_3521_, 2);
lean_dec_ref_known(v___x_3520_, 1);
v___x_3522_ = lean_box(v_binderInfo_3519_);
lean_inc(v_binderName_3516_);
lean_inc_ref(v_binderType_3517_);
v___f_3523_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0___boxed), 16, 6);
lean_closure_set(v___f_3523_, 0, v_body_3518_);
lean_closure_set(v___f_3523_, 1, v_binderType_3517_);
lean_closure_set(v___f_3523_, 2, v_a_3521_);
lean_closure_set(v___f_3523_, 3, v_binderName_3516_);
lean_closure_set(v___f_3523_, 4, v___x_3522_);
lean_closure_set(v___f_3523_, 5, v_e_3409_);
v___x_3524_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3521_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; lean_object* v___x_3526_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc_n(v_a_3525_, 2);
lean_dec_ref_known(v___x_3524_, 1);
v___x_3526_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_binderType_3517_, v_a_3525_, v_a_3410_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_cleanSuffix_3527_; lean_object* v___x_3528_; uint8_t v___y_3530_; lean_object* v___x_3533_; uint8_t v___x_3534_; 
lean_dec_ref_known(v___x_3526_, 1);
v_cleanSuffix_3527_ = lean_ctor_get(v_a_3410_, 2);
v___x_3528_ = lean_box(0);
v___x_3533_ = l_Lean_Expr_looseBVarRange(v_binderType_3517_);
lean_dec_ref(v_binderType_3517_);
v___x_3534_ = lean_nat_dec_le(v___x_3533_, v_cleanSuffix_3527_);
lean_dec(v___x_3533_);
if (v___x_3534_ == 0)
{
uint8_t v___x_3535_; 
v___x_3535_ = 1;
v___y_3530_ = v___x_3535_;
goto v___jp_3529_;
}
else
{
uint8_t v___x_3536_; 
v___x_3536_ = 0;
v___y_3530_ = v___x_3536_;
goto v___jp_3529_;
}
v___jp_3529_:
{
uint8_t v___x_3531_; lean_object* v___x_3532_; 
v___x_3531_ = 0;
v___x_3532_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_binderName_3516_, v_a_3525_, v___x_3528_, v___y_3530_, v___x_3531_, v___f_3523_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
return v___x_3532_;
}
}
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
lean_dec(v_a_3525_);
lean_dec_ref(v___f_3523_);
lean_dec_ref(v_binderType_3517_);
lean_dec(v_binderName_3516_);
v_a_3537_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3526_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3526_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
else
{
lean_dec_ref(v___f_3523_);
lean_dec_ref(v_binderType_3517_);
lean_dec(v_binderName_3516_);
return v___x_3524_;
}
}
else
{
lean_dec_ref(v_body_3518_);
lean_dec_ref(v_binderType_3517_);
lean_dec(v_binderName_3516_);
lean_dec_ref_known(v_e_3409_, 3);
return v___x_3520_;
}
}
case 7:
{
lean_object* v___x_3545_; 
v___x_3545_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(v_e_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
return v___x_3545_;
}
case 8:
{
lean_object* v_declName_3546_; lean_object* v_type_3547_; lean_object* v_value_3548_; lean_object* v_body_3549_; uint8_t v_nondep_3550_; lean_object* v___x_3551_; 
v_declName_3546_ = lean_ctor_get(v_e_3409_, 0);
lean_inc(v_declName_3546_);
v_type_3547_ = lean_ctor_get(v_e_3409_, 1);
lean_inc_ref_n(v_type_3547_, 2);
v_value_3548_ = lean_ctor_get(v_e_3409_, 2);
lean_inc_ref(v_value_3548_);
v_body_3549_ = lean_ctor_get(v_e_3409_, 3);
lean_inc_ref(v_body_3549_);
v_nondep_3550_ = lean_ctor_get_uint8(v_e_3409_, sizeof(void*)*4 + 8);
v___x_3551_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_type_3547_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3553_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3552_);
lean_dec_ref_known(v___x_3551_, 1);
lean_inc_ref(v_value_3548_);
v___x_3553_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_value_3548_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v___x_3555_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
lean_dec_ref_known(v___x_3553_, 1);
lean_inc(v_a_3552_);
v___x_3555_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3552_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3640_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3558_ = v___x_3555_;
v_isShared_3559_ = v_isSharedCheck_3640_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3555_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3640_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v_numCandidates_3560_; lean_object* v_cleanSuffix_3561_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; uint8_t v___y_3571_; lean_object* v___y_3572_; uint8_t v___y_3573_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___x_3603_; uint8_t v___x_3604_; 
v_numCandidates_3560_ = lean_ctor_get(v_a_3410_, 1);
v_cleanSuffix_3561_ = lean_ctor_get(v_a_3410_, 2);
v___x_3603_ = lean_unsigned_to_nat(0u);
v___x_3604_ = lean_nat_dec_lt(v___x_3603_, v_numCandidates_3560_);
if (v___x_3604_ == 0)
{
v___y_3589_ = v_a_3410_;
v___y_3590_ = v_a_3411_;
v___y_3591_ = v_a_3412_;
v___y_3592_ = v_a_3413_;
v___y_3593_ = v_a_3414_;
v___y_3594_ = v_a_3415_;
v___y_3595_ = v_a_3416_;
v___y_3596_ = v_a_3417_;
goto v___jp_3588_;
}
else
{
lean_object* v___x_3605_; 
lean_inc(v_a_3556_);
v___x_3605_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_type_3547_, v_a_3556_, v_a_3410_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v___x_3628_; uint8_t v___x_3629_; 
lean_dec_ref_known(v___x_3605_, 1);
v___x_3628_ = l_Lean_Expr_looseBVarRange(v_type_3547_);
v___x_3629_ = lean_nat_dec_le(v___x_3628_, v_cleanSuffix_3561_);
lean_dec(v___x_3628_);
if (v___x_3629_ == 0)
{
goto v___jp_3606_;
}
else
{
lean_object* v___x_3630_; uint8_t v___x_3631_; 
v___x_3630_ = l_Lean_Expr_looseBVarRange(v_value_3548_);
v___x_3631_ = lean_nat_dec_le(v___x_3630_, v_cleanSuffix_3561_);
lean_dec(v___x_3630_);
if (v___x_3631_ == 0)
{
goto v___jp_3606_;
}
else
{
v___y_3589_ = v_a_3410_;
v___y_3590_ = v_a_3411_;
v___y_3591_ = v_a_3412_;
v___y_3592_ = v_a_3413_;
v___y_3593_ = v_a_3414_;
v___y_3594_ = v_a_3415_;
v___y_3595_ = v_a_3416_;
v___y_3596_ = v_a_3417_;
goto v___jp_3588_;
}
}
v___jp_3606_:
{
uint8_t v___x_3607_; 
v___x_3607_ = l_Lean_Expr_isLambda(v_value_3548_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3608_; 
lean_inc_ref(v_value_3548_);
v___x_3608_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_value_3548_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; lean_object* v___x_3610_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___x_3608_, 1);
lean_inc(v_a_3556_);
v___x_3610_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_a_3609_, v_a_3556_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_dec_ref_known(v___x_3610_, 1);
v___y_3589_ = v_a_3410_;
v___y_3590_ = v_a_3411_;
v___y_3591_ = v_a_3412_;
v___y_3592_ = v_a_3413_;
v___y_3593_ = v_a_3414_;
v___y_3594_ = v_a_3415_;
v___y_3595_ = v_a_3416_;
v___y_3596_ = v_a_3417_;
goto v___jp_3588_;
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_del_object(v___x_3558_);
lean_dec(v_a_3556_);
lean_dec(v_a_3554_);
lean_dec(v_a_3552_);
lean_dec_ref(v_body_3549_);
lean_dec_ref(v_value_3548_);
lean_dec_ref(v_type_3547_);
lean_dec(v_declName_3546_);
lean_dec_ref_known(v_e_3409_, 4);
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3610_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3610_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
else
{
lean_del_object(v___x_3558_);
lean_dec(v_a_3556_);
lean_dec(v_a_3554_);
lean_dec(v_a_3552_);
lean_dec_ref(v_body_3549_);
lean_dec_ref(v_value_3548_);
lean_dec_ref(v_type_3547_);
lean_dec(v_declName_3546_);
lean_dec_ref_known(v_e_3409_, 4);
return v___x_3608_;
}
}
else
{
lean_object* v___x_3619_; 
lean_inc(v_a_3556_);
lean_inc_ref(v_value_3548_);
v___x_3619_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_value_3548_, v_a_3556_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_dec_ref_known(v___x_3619_, 1);
v___y_3589_ = v_a_3410_;
v___y_3590_ = v_a_3411_;
v___y_3591_ = v_a_3412_;
v___y_3592_ = v_a_3413_;
v___y_3593_ = v_a_3414_;
v___y_3594_ = v_a_3415_;
v___y_3595_ = v_a_3416_;
v___y_3596_ = v_a_3417_;
goto v___jp_3588_;
}
else
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3627_; 
lean_del_object(v___x_3558_);
lean_dec(v_a_3556_);
lean_dec(v_a_3554_);
lean_dec(v_a_3552_);
lean_dec_ref(v_body_3549_);
lean_dec_ref(v_value_3548_);
lean_dec_ref(v_type_3547_);
lean_dec(v_declName_3546_);
lean_dec_ref_known(v_e_3409_, 4);
v_a_3620_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___x_3619_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3619_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3625_; 
if (v_isShared_3623_ == 0)
{
v___x_3625_ = v___x_3622_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_del_object(v___x_3558_);
lean_dec(v_a_3556_);
lean_dec(v_a_3554_);
lean_dec(v_a_3552_);
lean_dec_ref(v_body_3549_);
lean_dec_ref(v_value_3548_);
lean_dec_ref(v_type_3547_);
lean_dec(v_declName_3546_);
lean_dec_ref_known(v_e_3409_, 4);
v_a_3632_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3605_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3605_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
v___jp_3562_:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___f_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3580_; 
v___x_3574_ = lean_box(v_nondep_3550_);
v___x_3575_ = lean_box(v___y_3573_);
lean_inc(v_declName_3546_);
lean_inc_ref(v_type_3547_);
v___f_3576_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1___boxed), 19, 9);
lean_closure_set(v___f_3576_, 0, v_body_3549_);
lean_closure_set(v___f_3576_, 1, v_type_3547_);
lean_closure_set(v___f_3576_, 2, v_a_3552_);
lean_closure_set(v___f_3576_, 3, v_declName_3546_);
lean_closure_set(v___f_3576_, 4, v_a_3554_);
lean_closure_set(v___f_3576_, 5, v___x_3574_);
lean_closure_set(v___f_3576_, 6, v_value_3548_);
lean_closure_set(v___f_3576_, 7, v_e_3409_);
lean_closure_set(v___f_3576_, 8, v___x_3575_);
v___x_3577_ = lean_box(v_nondep_3550_);
v___x_3578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___y_3572_);
lean_ctor_set(v___x_3578_, 1, v___x_3577_);
if (v_isShared_3559_ == 0)
{
lean_ctor_set_tag(v___x_3558_, 1);
lean_ctor_set(v___x_3558_, 0, v___x_3578_);
v___x_3580_ = v___x_3558_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3578_);
v___x_3580_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
if (v___y_3571_ == 0)
{
lean_object* v___x_3581_; uint8_t v___x_3582_; 
v___x_3581_ = l_Lean_Expr_looseBVarRange(v_type_3547_);
lean_dec_ref(v_type_3547_);
v___x_3582_ = lean_nat_dec_le(v___x_3581_, v_cleanSuffix_3561_);
lean_dec(v___x_3581_);
if (v___x_3582_ == 0)
{
uint8_t v___x_3583_; lean_object* v___x_3584_; 
v___x_3583_ = 1;
v___x_3584_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_declName_3546_, v_a_3556_, v___x_3580_, v___x_3583_, v___y_3573_, v___f_3576_, v___y_3570_, v___y_3563_, v___y_3566_, v___y_3565_, v___y_3567_, v___y_3564_, v___y_3568_, v___y_3569_);
return v___x_3584_;
}
else
{
lean_object* v___x_3585_; 
v___x_3585_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_declName_3546_, v_a_3556_, v___x_3580_, v___y_3571_, v___y_3573_, v___f_3576_, v___y_3570_, v___y_3563_, v___y_3566_, v___y_3565_, v___y_3567_, v___y_3564_, v___y_3568_, v___y_3569_);
return v___x_3585_;
}
}
else
{
lean_object* v___x_3586_; 
lean_dec_ref(v_type_3547_);
v___x_3586_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_declName_3546_, v_a_3556_, v___x_3580_, v___y_3571_, v___y_3573_, v___f_3576_, v___y_3570_, v___y_3563_, v___y_3566_, v___y_3565_, v___y_3567_, v___y_3564_, v___y_3568_, v___y_3569_);
return v___x_3586_;
}
}
}
v___jp_3588_:
{
lean_object* v___x_3597_; 
lean_inc(v_a_3554_);
v___x_3597_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3554_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
if (lean_obj_tag(v___x_3597_) == 0)
{
if (v_nondep_3550_ == 0)
{
lean_object* v_a_3598_; uint8_t v___x_3599_; uint8_t v___x_3600_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3598_);
lean_dec_ref_known(v___x_3597_, 1);
v___x_3599_ = 1;
v___x_3600_ = l_Lean_Expr_hasExprMVar(v_e_3409_);
if (v___x_3600_ == 0)
{
v___y_3563_ = v___y_3590_;
v___y_3564_ = v___y_3594_;
v___y_3565_ = v___y_3592_;
v___y_3566_ = v___y_3591_;
v___y_3567_ = v___y_3593_;
v___y_3568_ = v___y_3595_;
v___y_3569_ = v___y_3596_;
v___y_3570_ = v___y_3589_;
v___y_3571_ = v___x_3599_;
v___y_3572_ = v_a_3598_;
v___y_3573_ = v___x_3599_;
goto v___jp_3562_;
}
else
{
v___y_3563_ = v___y_3590_;
v___y_3564_ = v___y_3594_;
v___y_3565_ = v___y_3592_;
v___y_3566_ = v___y_3591_;
v___y_3567_ = v___y_3593_;
v___y_3568_ = v___y_3595_;
v___y_3569_ = v___y_3596_;
v___y_3570_ = v___y_3589_;
v___y_3571_ = v___x_3599_;
v___y_3572_ = v_a_3598_;
v___y_3573_ = v_nondep_3550_;
goto v___jp_3562_;
}
}
else
{
lean_object* v_a_3601_; uint8_t v___x_3602_; 
v_a_3601_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3601_);
lean_dec_ref_known(v___x_3597_, 1);
v___x_3602_ = 0;
v___y_3563_ = v___y_3590_;
v___y_3564_ = v___y_3594_;
v___y_3565_ = v___y_3592_;
v___y_3566_ = v___y_3591_;
v___y_3567_ = v___y_3593_;
v___y_3568_ = v___y_3595_;
v___y_3569_ = v___y_3596_;
v___y_3570_ = v___y_3589_;
v___y_3571_ = v___x_3602_;
v___y_3572_ = v_a_3601_;
v___y_3573_ = v___x_3602_;
goto v___jp_3562_;
}
}
else
{
lean_del_object(v___x_3558_);
lean_dec(v_a_3556_);
lean_dec(v_a_3554_);
lean_dec(v_a_3552_);
lean_dec_ref(v_body_3549_);
lean_dec_ref(v_value_3548_);
lean_dec_ref(v_type_3547_);
lean_dec(v_declName_3546_);
lean_dec_ref_known(v_e_3409_, 4);
return v___x_3597_;
}
}
}
}
else
{
lean_dec(v_a_3554_);
lean_dec(v_a_3552_);
lean_dec_ref(v_body_3549_);
lean_dec_ref(v_value_3548_);
lean_dec_ref(v_type_3547_);
lean_dec(v_declName_3546_);
lean_dec_ref_known(v_e_3409_, 4);
return v___x_3555_;
}
}
else
{
lean_dec(v_a_3552_);
lean_dec_ref(v_body_3549_);
lean_dec_ref(v_value_3548_);
lean_dec_ref(v_type_3547_);
lean_dec(v_declName_3546_);
lean_dec_ref_known(v_e_3409_, 4);
return v___x_3553_;
}
}
else
{
lean_dec_ref(v_body_3549_);
lean_dec_ref(v_value_3548_);
lean_dec_ref(v_type_3547_);
lean_dec(v_declName_3546_);
lean_dec_ref_known(v_e_3409_, 4);
return v___x_3551_;
}
}
default: 
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
lean_dec_ref(v_e_3409_);
v___x_3641_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1);
v___x_3642_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(v___x_3641_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
return v___x_3642_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3409_ = stack[0].m_obj;
lean_object* v_a_3410_ = stack[1].m_obj;
lean_object* v_a_3411_ = stack[2].m_obj;
lean_object* v_a_3412_ = stack[3].m_obj;
lean_object* v_a_3413_ = stack[4].m_obj;
lean_object* v_a_3414_ = stack[5].m_obj;
lean_object* v_a_3415_ = stack[6].m_obj;
lean_object* v_a_3416_ = stack[7].m_obj;
lean_object* v_a_3417_ = stack[8].m_obj;
lean_object* v_res_3643_;
v_res_3643_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(v_e_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
stack->m_obj
 = v_res_3643_;
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(lean_object* v_e_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_){
_start:
{
lean_object* v___x_3653_; lean_object* v_visitedClosed_3654_; lean_object* v___x_3655_; 
v___x_3653_ = lean_st_ref_get(v_a_3645_);
v_visitedClosed_3654_ = lean_ctor_get(v___x_3653_, 3);
lean_inc_ref(v_visitedClosed_3654_);
lean_dec(v___x_3653_);
v___x_3655_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_visitedClosed_3654_, v_e_3644_);
lean_dec_ref(v_visitedClosed_3654_);
if (lean_obj_tag(v___x_3655_) == 1)
{
lean_object* v_val_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
lean_dec_ref(v_e_3644_);
v_val_3656_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___x_3655_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_val_3656_);
lean_dec(v___x_3655_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
lean_ctor_set_tag(v___x_3658_, 0);
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_val_3656_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
else
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v_visited_3666_; lean_object* v_types_3667_; lean_object* v_subst_3668_; lean_object* v_visitedClosed_3669_; lean_object* v_hasDepLetCache_3670_; lean_object* v_numConverted_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3741_; 
lean_dec(v___x_3655_);
v___x_3664_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2);
v___x_3665_ = lean_st_ref_take(v_a_3645_);
v_visited_3666_ = lean_ctor_get(v___x_3665_, 0);
v_types_3667_ = lean_ctor_get(v___x_3665_, 1);
v_subst_3668_ = lean_ctor_get(v___x_3665_, 2);
v_visitedClosed_3669_ = lean_ctor_get(v___x_3665_, 3);
v_hasDepLetCache_3670_ = lean_ctor_get(v___x_3665_, 4);
v_numConverted_3671_ = lean_ctor_get(v___x_3665_, 5);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3673_ = v___x_3665_;
v_isShared_3674_ = v_isSharedCheck_3741_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_numConverted_3671_);
lean_inc(v_hasDepLetCache_3670_);
lean_inc(v_visitedClosed_3669_);
lean_inc(v_subst_3668_);
lean_inc(v_types_3667_);
lean_inc(v_visited_3666_);
lean_dec(v___x_3665_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3741_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3675_; lean_object* v___x_3677_; 
v___x_3675_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 2, v___x_3675_);
lean_ctor_set(v___x_3673_, 1, v___x_3675_);
lean_ctor_set(v___x_3673_, 0, v___x_3675_);
v___x_3677_ = v___x_3673_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3675_);
lean_ctor_set(v_reuseFailAlloc_3740_, 1, v___x_3675_);
lean_ctor_set(v_reuseFailAlloc_3740_, 2, v___x_3675_);
lean_ctor_set(v_reuseFailAlloc_3740_, 3, v_visitedClosed_3669_);
lean_ctor_set(v_reuseFailAlloc_3740_, 4, v_hasDepLetCache_3670_);
lean_ctor_set(v_reuseFailAlloc_3740_, 5, v_numConverted_3671_);
v___x_3677_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
lean_object* v___x_3678_; lean_object* v_r_3679_; 
v___x_3678_ = lean_st_ref_put(v_a_3645_, v___x_3677_);
lean_inc_ref(v_e_3644_);
v_r_3679_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(v_e_3644_, v___x_3664_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_);
if (lean_obj_tag(v_r_3679_) == 0)
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3720_; 
v_a_3680_ = lean_ctor_get(v_r_3679_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v_r_3679_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3682_ = v_r_3679_;
v_isShared_3683_ = v_isSharedCheck_3720_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v_r_3679_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3720_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
lean_inc(v_a_3680_);
if (v_isShared_3683_ == 0)
{
lean_ctor_set_tag(v___x_3682_, 1);
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_a_3680_);
v___x_3685_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
lean_object* v___x_3686_; 
v___x_3686_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(v_a_3645_, v_visited_3666_, v_types_3667_, v_subst_3668_, v___x_3685_);
lean_dec_ref(v___x_3685_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3709_; 
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3709_ == 0)
{
lean_object* v_unused_3710_; 
v_unused_3710_ = lean_ctor_get(v___x_3686_, 0);
lean_dec(v_unused_3710_);
v___x_3688_ = v___x_3686_;
v_isShared_3689_ = v_isSharedCheck_3709_;
goto v_resetjp_3687_;
}
else
{
lean_dec(v___x_3686_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3709_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3690_; lean_object* v_visited_3691_; lean_object* v_types_3692_; lean_object* v_subst_3693_; lean_object* v_visitedClosed_3694_; lean_object* v_hasDepLetCache_3695_; lean_object* v_numConverted_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3708_; 
v___x_3690_ = lean_st_ref_take(v_a_3645_);
v_visited_3691_ = lean_ctor_get(v___x_3690_, 0);
v_types_3692_ = lean_ctor_get(v___x_3690_, 1);
v_subst_3693_ = lean_ctor_get(v___x_3690_, 2);
v_visitedClosed_3694_ = lean_ctor_get(v___x_3690_, 3);
v_hasDepLetCache_3695_ = lean_ctor_get(v___x_3690_, 4);
v_numConverted_3696_ = lean_ctor_get(v___x_3690_, 5);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3698_ = v___x_3690_;
v_isShared_3699_ = v_isSharedCheck_3708_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_numConverted_3696_);
lean_inc(v_hasDepLetCache_3695_);
lean_inc(v_visitedClosed_3694_);
lean_inc(v_subst_3693_);
lean_inc(v_types_3692_);
lean_inc(v_visited_3691_);
lean_dec(v___x_3690_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3708_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3700_; lean_object* v___x_3702_; 
lean_inc(v_a_3680_);
v___x_3700_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_visitedClosed_3694_, v_e_3644_, v_a_3680_);
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 3, v___x_3700_);
v___x_3702_ = v___x_3698_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_visited_3691_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v_types_3692_);
lean_ctor_set(v_reuseFailAlloc_3707_, 2, v_subst_3693_);
lean_ctor_set(v_reuseFailAlloc_3707_, 3, v___x_3700_);
lean_ctor_set(v_reuseFailAlloc_3707_, 4, v_hasDepLetCache_3695_);
lean_ctor_set(v_reuseFailAlloc_3707_, 5, v_numConverted_3696_);
v___x_3702_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
lean_object* v___x_3703_; lean_object* v___x_3705_; 
v___x_3703_ = lean_st_ref_put(v_a_3645_, v___x_3702_);
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 0, v_a_3680_);
v___x_3705_ = v___x_3688_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3680_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_dec(v_a_3680_);
lean_dec_ref(v_e_3644_);
v_a_3711_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3686_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3686_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
lean_dec_ref(v_e_3644_);
v_a_3721_ = lean_ctor_get(v_r_3679_, 0);
lean_inc(v_a_3721_);
lean_dec_ref_known(v_r_3679_, 1);
v___x_3722_ = lean_box(0);
v___x_3723_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(v_a_3645_, v_visited_3666_, v_types_3667_, v_subst_3668_, v___x_3722_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3730_ == 0)
{
lean_object* v_unused_3731_; 
v_unused_3731_ = lean_ctor_get(v___x_3723_, 0);
lean_dec(v_unused_3731_);
v___x_3725_ = v___x_3723_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_dec(v___x_3723_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
lean_ctor_set_tag(v___x_3725_, 1);
lean_ctor_set(v___x_3725_, 0, v_a_3721_);
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3721_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec(v_a_3721_);
v_a_3732_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3723_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3723_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3644_ = stack[0].m_obj;
lean_object* v_a_3645_ = stack[1].m_obj;
lean_object* v_a_3646_ = stack[2].m_obj;
lean_object* v_a_3647_ = stack[3].m_obj;
lean_object* v_a_3648_ = stack[4].m_obj;
lean_object* v_a_3649_ = stack[5].m_obj;
lean_object* v_a_3650_ = stack[6].m_obj;
lean_object* v_a_3651_ = stack[7].m_obj;
lean_object* v_res_3742_;
v_res_3742_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(v_e_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_);
stack->m_obj
 = v_res_3742_;
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(lean_object* v_e_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_){
_start:
{
lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; 
switch(lean_obj_tag(v_e_3743_))
{
case 0:
{
lean_object* v___x_3819_; 
v___x_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3819_, 0, v_e_3743_);
return v___x_3819_;
}
case 1:
{
lean_object* v___x_3820_; 
v___x_3820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3820_, 0, v_e_3743_);
return v___x_3820_;
}
case 2:
{
lean_object* v___x_3821_; 
v___x_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3821_, 0, v_e_3743_);
return v___x_3821_;
}
case 3:
{
lean_object* v___x_3822_; 
v___x_3822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3822_, 0, v_e_3743_);
return v___x_3822_;
}
case 4:
{
lean_object* v___x_3823_; 
v___x_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3823_, 0, v_e_3743_);
return v___x_3823_;
}
case 9:
{
lean_object* v___x_3824_; 
v___x_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3824_, 0, v_e_3743_);
return v___x_3824_;
}
default: 
{
lean_object* v_numCandidates_3825_; lean_object* v_cleanSuffix_3826_; lean_object* v___x_3827_; uint8_t v___x_3828_; 
v_numCandidates_3825_ = lean_ctor_get(v_a_3744_, 1);
v_cleanSuffix_3826_ = lean_ctor_get(v_a_3744_, 2);
v___x_3827_ = lean_unsigned_to_nat(0u);
v___x_3828_ = lean_nat_dec_eq(v_numCandidates_3825_, v___x_3827_);
if (v___x_3828_ == 0)
{
lean_object* v___x_3829_; uint8_t v___x_3830_; 
v___x_3829_ = l_Lean_Expr_looseBVarRange(v_e_3743_);
v___x_3830_ = lean_nat_dec_le(v___x_3829_, v_cleanSuffix_3826_);
lean_dec(v___x_3829_);
if (v___x_3830_ == 0)
{
v___y_3754_ = v_a_3744_;
v___y_3755_ = v_a_3745_;
v___y_3756_ = v_a_3746_;
v___y_3757_ = v_a_3747_;
v___y_3758_ = v_a_3748_;
v___y_3759_ = v_a_3749_;
v___y_3760_ = v_a_3750_;
v___y_3761_ = v_a_3751_;
goto v___jp_3753_;
}
else
{
goto v___jp_3800_;
}
}
else
{
goto v___jp_3800_;
}
}
}
v___jp_3753_:
{
uint8_t v___x_3762_; 
v___x_3762_ = l_Lean_Expr_hasLooseBVars(v_e_3743_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3763_; 
v___x_3763_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(v_e_3743_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
return v___x_3763_;
}
else
{
lean_object* v___x_3764_; lean_object* v_visited_3765_; lean_object* v___x_3766_; 
v___x_3764_ = lean_st_ref_get(v___y_3755_);
v_visited_3765_ = lean_ctor_get(v___x_3764_, 0);
lean_inc_ref(v_visited_3765_);
lean_dec(v___x_3764_);
v___x_3766_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_visited_3765_, v_e_3743_);
lean_dec_ref(v_visited_3765_);
if (lean_obj_tag(v___x_3766_) == 1)
{
lean_object* v_val_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_dec_ref(v_e_3743_);
v_val_3767_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3766_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_val_3767_);
lean_dec(v___x_3766_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
lean_ctor_set_tag(v___x_3769_, 0);
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_val_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
else
{
lean_object* v___x_3775_; 
lean_dec(v___x_3766_);
lean_inc_ref(v_e_3743_);
v___x_3775_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(v_e_3743_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3799_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3778_ = v___x_3775_;
v_isShared_3779_ = v_isSharedCheck_3799_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3775_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3799_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3780_; lean_object* v_visited_3781_; lean_object* v_types_3782_; lean_object* v_subst_3783_; lean_object* v_visitedClosed_3784_; lean_object* v_hasDepLetCache_3785_; lean_object* v_numConverted_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3798_; 
v___x_3780_ = lean_st_ref_take(v___y_3755_);
v_visited_3781_ = lean_ctor_get(v___x_3780_, 0);
v_types_3782_ = lean_ctor_get(v___x_3780_, 1);
v_subst_3783_ = lean_ctor_get(v___x_3780_, 2);
v_visitedClosed_3784_ = lean_ctor_get(v___x_3780_, 3);
v_hasDepLetCache_3785_ = lean_ctor_get(v___x_3780_, 4);
v_numConverted_3786_ = lean_ctor_get(v___x_3780_, 5);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3788_ = v___x_3780_;
v_isShared_3789_ = v_isSharedCheck_3798_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_numConverted_3786_);
lean_inc(v_hasDepLetCache_3785_);
lean_inc(v_visitedClosed_3784_);
lean_inc(v_subst_3783_);
lean_inc(v_types_3782_);
lean_inc(v_visited_3781_);
lean_dec(v___x_3780_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3798_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3790_; lean_object* v___x_3792_; 
lean_inc(v_a_3776_);
v___x_3790_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_visited_3781_, v_e_3743_, v_a_3776_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 0, v___x_3790_);
v___x_3792_ = v___x_3788_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v___x_3790_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v_types_3782_);
lean_ctor_set(v_reuseFailAlloc_3797_, 2, v_subst_3783_);
lean_ctor_set(v_reuseFailAlloc_3797_, 3, v_visitedClosed_3784_);
lean_ctor_set(v_reuseFailAlloc_3797_, 4, v_hasDepLetCache_3785_);
lean_ctor_set(v_reuseFailAlloc_3797_, 5, v_numConverted_3786_);
v___x_3792_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
lean_object* v___x_3793_; lean_object* v___x_3795_; 
v___x_3793_ = lean_st_ref_put(v___y_3755_, v___x_3792_);
if (v_isShared_3779_ == 0)
{
v___x_3795_ = v___x_3778_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_a_3776_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3743_);
return v___x_3775_;
}
}
}
}
v___jp_3800_:
{
lean_object* v___x_3801_; 
lean_inc_ref(v_e_3743_);
v___x_3801_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_e_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3810_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3804_ = v___x_3801_;
v_isShared_3805_ = v_isSharedCheck_3810_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3801_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3810_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
uint8_t v___x_3806_; 
v___x_3806_ = lean_unbox(v_a_3802_);
lean_dec(v_a_3802_);
if (v___x_3806_ == 0)
{
lean_object* v___x_3808_; 
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 0, v_e_3743_);
v___x_3808_ = v___x_3804_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_e_3743_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
else
{
lean_del_object(v___x_3804_);
v___y_3754_ = v_a_3744_;
v___y_3755_ = v_a_3745_;
v___y_3756_ = v_a_3746_;
v___y_3757_ = v_a_3747_;
v___y_3758_ = v_a_3748_;
v___y_3759_ = v_a_3749_;
v___y_3760_ = v_a_3750_;
v___y_3761_ = v_a_3751_;
goto v___jp_3753_;
}
}
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
lean_dec_ref(v_e_3743_);
v_a_3811_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3801_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3801_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3743_ = stack[0].m_obj;
lean_object* v_a_3744_ = stack[1].m_obj;
lean_object* v_a_3745_ = stack[2].m_obj;
lean_object* v_a_3746_ = stack[3].m_obj;
lean_object* v_a_3747_ = stack[4].m_obj;
lean_object* v_a_3748_ = stack[5].m_obj;
lean_object* v_a_3749_ = stack[6].m_obj;
lean_object* v_a_3750_ = stack[7].m_obj;
lean_object* v_a_3751_ = stack[8].m_obj;
lean_object* v_res_3831_;
v_res_3831_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_e_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
stack->m_obj
 = v_res_3831_;
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0(lean_object* v_body_3832_, lean_object* v_binderType_3833_, lean_object* v_a_3834_, lean_object* v_binderName_3835_, uint8_t v_binderInfo_3836_, lean_object* v_e_3837_, lean_object* v_x_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v___x_3848_; 
lean_inc_ref(v_body_3832_);
v___x_3848_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_body_3832_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3864_; 
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3851_ = v___x_3848_;
v_isShared_3852_ = v_isSharedCheck_3864_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3848_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3864_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
size_t v___x_3853_; size_t v___x_3854_; uint8_t v___x_3855_; 
v___x_3853_ = lean_ptr_addr(v_binderType_3833_);
v___x_3854_ = lean_ptr_addr(v_a_3834_);
v___x_3855_ = lean_usize_dec_eq(v___x_3853_, v___x_3854_);
if (v___x_3855_ == 0)
{
lean_object* v___x_3856_; 
lean_del_object(v___x_3851_);
lean_dec_ref(v_e_3837_);
lean_dec_ref(v_body_3832_);
v___x_3856_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(v_binderName_3835_, v_binderInfo_3836_, v_a_3834_, v_a_3849_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
return v___x_3856_;
}
else
{
size_t v___x_3857_; size_t v___x_3858_; uint8_t v___x_3859_; 
v___x_3857_ = lean_ptr_addr(v_body_3832_);
lean_dec_ref(v_body_3832_);
v___x_3858_ = lean_ptr_addr(v_a_3849_);
v___x_3859_ = lean_usize_dec_eq(v___x_3857_, v___x_3858_);
if (v___x_3859_ == 0)
{
lean_object* v___x_3860_; 
lean_del_object(v___x_3851_);
lean_dec_ref(v_e_3837_);
v___x_3860_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(v_binderName_3835_, v_binderInfo_3836_, v_a_3834_, v_a_3849_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
return v___x_3860_;
}
else
{
lean_object* v___x_3862_; 
lean_dec(v_a_3849_);
lean_dec(v_binderName_3835_);
lean_dec_ref(v_a_3834_);
if (v_isShared_3852_ == 0)
{
lean_ctor_set(v___x_3851_, 0, v_e_3837_);
v___x_3862_ = v___x_3851_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_e_3837_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3837_);
lean_dec(v_binderName_3835_);
lean_dec_ref(v_a_3834_);
lean_dec_ref(v_body_3832_);
return v___x_3848_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_3832_ = stack[0].m_obj;
lean_object* v_binderType_3833_ = stack[1].m_obj;
lean_object* v_a_3834_ = stack[2].m_obj;
lean_object* v_binderName_3835_ = stack[3].m_obj;
uint8_t v_binderInfo_3836_ = stack[4].m_num;
lean_object* v_e_3837_ = stack[5].m_obj;
lean_object* v_x_3838_ = stack[6].m_obj;
lean_object* v___y_3839_ = stack[7].m_obj;
lean_object* v___y_3840_ = stack[8].m_obj;
lean_object* v___y_3841_ = stack[9].m_obj;
lean_object* v___y_3842_ = stack[10].m_obj;
lean_object* v___y_3843_ = stack[11].m_obj;
lean_object* v___y_3844_ = stack[12].m_obj;
lean_object* v___y_3845_ = stack[13].m_obj;
lean_object* v___y_3846_ = stack[14].m_obj;
lean_object* v_res_3865_;
v_res_3865_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0(v_body_3832_, v_binderType_3833_, v_a_3834_, v_binderName_3835_, v_binderInfo_3836_, v_e_3837_, v_x_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
stack->m_obj
 = v_res_3865_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___boxed(lean_object* v_e_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(v_e_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_);
lean_dec(v_a_3874_);
lean_dec_ref(v_a_3873_);
lean_dec(v_a_3872_);
lean_dec_ref(v_a_3871_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec(v_a_3868_);
lean_dec_ref(v_a_3867_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___boxed(lean_object* v_e_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(v_e_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_);
lean_dec(v_a_3884_);
lean_dec_ref(v_a_3883_);
lean_dec(v_a_3882_);
lean_dec_ref(v_a_3881_);
lean_dec(v_a_3880_);
lean_dec_ref(v_a_3879_);
lean_dec(v_a_3878_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit___boxed(lean_object* v_e_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_e_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_);
lean_dec(v_a_3895_);
lean_dec_ref(v_a_3894_);
lean_dec(v_a_3893_);
lean_dec_ref(v_a_3892_);
lean_dec(v_a_3891_);
lean_dec_ref(v_a_3890_);
lean_dec(v_a_3889_);
lean_dec_ref(v_a_3888_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___boxed(lean_object* v_e_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(v_e_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
lean_dec(v_a_3906_);
lean_dec_ref(v_a_3905_);
lean_dec(v_a_3904_);
lean_dec_ref(v_a_3903_);
lean_dec(v_a_3902_);
lean_dec_ref(v_a_3901_);
lean_dec(v_a_3900_);
lean_dec_ref(v_a_3899_);
return v_res_3908_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1(lean_object* v_f_3909_, lean_object* v_a_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(v_f_3909_, v_a_3910_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_);
return v___x_3920_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3909_ = stack[0].m_obj;
lean_object* v_a_3910_ = stack[1].m_obj;
lean_object* v___y_3911_ = stack[2].m_obj;
lean_object* v___y_3912_ = stack[3].m_obj;
lean_object* v___y_3913_ = stack[4].m_obj;
lean_object* v___y_3914_ = stack[5].m_obj;
lean_object* v___y_3915_ = stack[6].m_obj;
lean_object* v___y_3916_ = stack[7].m_obj;
lean_object* v___y_3917_ = stack[8].m_obj;
lean_object* v___y_3918_ = stack[9].m_obj;
lean_object* v_res_3921_;
v_res_3921_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1(v_f_3909_, v_a_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_);
stack->m_obj
 = v_res_3921_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___boxed(lean_object* v_f_3922_, lean_object* v_a_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
lean_object* v_res_3933_; 
v_res_3933_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1(v_f_3922_, v_a_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
return v_res_3933_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2(lean_object* v_d_3934_, lean_object* v_e_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_){
_start:
{
lean_object* v___x_3945_; 
v___x_3945_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(v_d_3934_, v_e_3935_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
return v___x_3945_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_3934_ = stack[0].m_obj;
lean_object* v_e_3935_ = stack[1].m_obj;
lean_object* v___y_3936_ = stack[2].m_obj;
lean_object* v___y_3937_ = stack[3].m_obj;
lean_object* v___y_3938_ = stack[4].m_obj;
lean_object* v___y_3939_ = stack[5].m_obj;
lean_object* v___y_3940_ = stack[6].m_obj;
lean_object* v___y_3941_ = stack[7].m_obj;
lean_object* v___y_3942_ = stack[8].m_obj;
lean_object* v___y_3943_ = stack[9].m_obj;
lean_object* v_res_3946_;
v_res_3946_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2(v_d_3934_, v_e_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
stack->m_obj
 = v_res_3946_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___boxed(lean_object* v_d_3947_, lean_object* v_e_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2(v_d_3947_, v_e_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
return v_res_3958_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3(lean_object* v_structName_3959_, lean_object* v_idx_3960_, lean_object* v_struct_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v___x_3971_; 
v___x_3971_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(v_structName_3959_, v_idx_3960_, v_struct_3961_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
return v___x_3971_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_structName_3959_ = stack[0].m_obj;
lean_object* v_idx_3960_ = stack[1].m_obj;
lean_object* v_struct_3961_ = stack[2].m_obj;
lean_object* v___y_3962_ = stack[3].m_obj;
lean_object* v___y_3963_ = stack[4].m_obj;
lean_object* v___y_3964_ = stack[5].m_obj;
lean_object* v___y_3965_ = stack[6].m_obj;
lean_object* v___y_3966_ = stack[7].m_obj;
lean_object* v___y_3967_ = stack[8].m_obj;
lean_object* v___y_3968_ = stack[9].m_obj;
lean_object* v___y_3969_ = stack[10].m_obj;
lean_object* v_res_3972_;
v_res_3972_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3(v_structName_3959_, v_idx_3960_, v_struct_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
stack->m_obj
 = v_res_3972_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___boxed(lean_object* v_structName_3973_, lean_object* v_idx_3974_, lean_object* v_struct_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3(v_structName_3973_, v_idx_3974_, v_struct_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
return v_res_3985_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4(lean_object* v_x_3986_, uint8_t v_bi_3987_, lean_object* v_t_3988_, lean_object* v_b_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v___x_3999_; 
v___x_3999_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(v_x_3986_, v_bi_3987_, v_t_3988_, v_b_3989_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
return v___x_3999_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3986_ = stack[0].m_obj;
uint8_t v_bi_3987_ = stack[1].m_num;
lean_object* v_t_3988_ = stack[2].m_obj;
lean_object* v_b_3989_ = stack[3].m_obj;
lean_object* v___y_3990_ = stack[4].m_obj;
lean_object* v___y_3991_ = stack[5].m_obj;
lean_object* v___y_3992_ = stack[6].m_obj;
lean_object* v___y_3993_ = stack[7].m_obj;
lean_object* v___y_3994_ = stack[8].m_obj;
lean_object* v___y_3995_ = stack[9].m_obj;
lean_object* v___y_3996_ = stack[10].m_obj;
lean_object* v___y_3997_ = stack[11].m_obj;
lean_object* v_res_4000_;
v_res_4000_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4(v_x_3986_, v_bi_3987_, v_t_3988_, v_b_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
stack->m_obj
 = v_res_4000_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___boxed(lean_object* v_x_4001_, lean_object* v_bi_4002_, lean_object* v_t_4003_, lean_object* v_b_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
uint8_t v_bi_boxed_4014_; lean_object* v_res_4015_; 
v_bi_boxed_4014_ = lean_unbox(v_bi_4002_);
v_res_4015_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4(v_x_4001_, v_bi_boxed_4014_, v_t_4003_, v_b_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
return v_res_4015_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5(lean_object* v_x_4016_, lean_object* v_t_4017_, lean_object* v_v_4018_, lean_object* v_b_4019_, uint8_t v_nondep_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
lean_object* v___x_4030_; 
v___x_4030_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_x_4016_, v_t_4017_, v_v_4018_, v_b_4019_, v_nondep_4020_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
return v___x_4030_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4016_ = stack[0].m_obj;
lean_object* v_t_4017_ = stack[1].m_obj;
lean_object* v_v_4018_ = stack[2].m_obj;
lean_object* v_b_4019_ = stack[3].m_obj;
uint8_t v_nondep_4020_ = stack[4].m_num;
lean_object* v___y_4021_ = stack[5].m_obj;
lean_object* v___y_4022_ = stack[6].m_obj;
lean_object* v___y_4023_ = stack[7].m_obj;
lean_object* v___y_4024_ = stack[8].m_obj;
lean_object* v___y_4025_ = stack[9].m_obj;
lean_object* v___y_4026_ = stack[10].m_obj;
lean_object* v___y_4027_ = stack[11].m_obj;
lean_object* v___y_4028_ = stack[12].m_obj;
lean_object* v_res_4031_;
v_res_4031_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5(v_x_4016_, v_t_4017_, v_v_4018_, v_b_4019_, v_nondep_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
stack->m_obj
 = v_res_4031_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___boxed(lean_object* v_x_4032_, lean_object* v_t_4033_, lean_object* v_v_4034_, lean_object* v_b_4035_, lean_object* v_nondep_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
uint8_t v_nondep_boxed_4046_; lean_object* v_res_4047_; 
v_nondep_boxed_4046_ = lean_unbox(v_nondep_4036_);
v_res_4047_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5(v_x_4032_, v_t_4033_, v_v_4034_, v_b_4035_, v_nondep_boxed_4046_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
return v_res_4047_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8(lean_object* v_x_4048_, uint8_t v_bi_4049_, lean_object* v_t_4050_, lean_object* v_b_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
lean_object* v___x_4061_; 
v___x_4061_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(v_x_4048_, v_bi_4049_, v_t_4050_, v_b_4051_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
return v___x_4061_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4048_ = stack[0].m_obj;
uint8_t v_bi_4049_ = stack[1].m_num;
lean_object* v_t_4050_ = stack[2].m_obj;
lean_object* v_b_4051_ = stack[3].m_obj;
lean_object* v___y_4052_ = stack[4].m_obj;
lean_object* v___y_4053_ = stack[5].m_obj;
lean_object* v___y_4054_ = stack[6].m_obj;
lean_object* v___y_4055_ = stack[7].m_obj;
lean_object* v___y_4056_ = stack[8].m_obj;
lean_object* v___y_4057_ = stack[9].m_obj;
lean_object* v___y_4058_ = stack[10].m_obj;
lean_object* v___y_4059_ = stack[11].m_obj;
lean_object* v_res_4062_;
v_res_4062_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8(v_x_4048_, v_bi_4049_, v_t_4050_, v_b_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
stack->m_obj
 = v_res_4062_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___boxed(lean_object* v_x_4063_, lean_object* v_bi_4064_, lean_object* v_t_4065_, lean_object* v_b_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
uint8_t v_bi_boxed_4076_; lean_object* v_res_4077_; 
v_bi_boxed_4076_ = lean_unbox(v_bi_4064_);
v_res_4077_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8(v_x_4063_, v_bi_boxed_4076_, v_t_4065_, v_b_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
return v_res_4077_;
}
}
lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed(lean_object* v_e_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_){
_start:
{
lean_object* v___x_4088_; 
v___x_4088_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(v_e_4078_, v_a_4080_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
return v___x_4088_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4078_ = stack[0].m_obj;
lean_object* v_a_4079_ = stack[1].m_obj;
lean_object* v_a_4080_ = stack[2].m_obj;
lean_object* v_a_4081_ = stack[3].m_obj;
lean_object* v_a_4082_ = stack[4].m_obj;
lean_object* v_a_4083_ = stack[5].m_obj;
lean_object* v_a_4084_ = stack[6].m_obj;
lean_object* v_a_4085_ = stack[7].m_obj;
lean_object* v_a_4086_ = stack[8].m_obj;
lean_object* v_res_4089_;
v_res_4089_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed(v_e_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
stack->m_obj
 = v_res_4089_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___boxed(lean_object* v_e_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed(v_e_4090_, v_a_4091_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
lean_dec(v_a_4098_);
lean_dec_ref(v_a_4097_);
lean_dec(v_a_4096_);
lean_dec_ref(v_a_4095_);
lean_dec(v_a_4094_);
lean_dec_ref(v_a_4093_);
lean_dec(v_a_4092_);
lean_dec_ref(v_a_4091_);
return v_res_4100_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6(lean_object* v_00_u03b2_4101_, lean_object* v_k_4102_, lean_object* v_t_4103_){
_start:
{
uint8_t v___x_4104_; 
v___x_4104_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(v_k_4102_, v_t_4103_);
return v___x_4104_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_4102_ = stack[1].m_obj;
lean_object* v_t_4103_ = stack[2].m_obj;
uint8_t v_res_4105_;
v_res_4105_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6(lean_box(0), v_k_4102_, v_t_4103_);
stack->m_num = v_res_4105_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___boxed(lean_object* v_00_u03b2_4106_, lean_object* v_k_4107_, lean_object* v_t_4108_){
_start:
{
uint8_t v_res_4109_; lean_object* v_r_4110_; 
v_res_4109_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6(v_00_u03b2_4106_, v_k_4107_, v_t_4108_);
lean_dec(v_t_4108_);
lean_dec(v_k_4107_);
v_r_4110_ = lean_box(v_res_4109_);
return v_r_4110_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0(lean_object* v_x_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v___x_4119_; 
lean_inc(v___y_4113_);
lean_inc_ref(v___y_4112_);
v___x_4119_ = lean_apply_7(v_x_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, lean_box(0));
return v___x_4119_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4111_ = stack[0].m_obj;
lean_object* v___y_4112_ = stack[1].m_obj;
lean_object* v___y_4113_ = stack[2].m_obj;
lean_object* v___y_4114_ = stack[3].m_obj;
lean_object* v___y_4115_ = stack[4].m_obj;
lean_object* v___y_4116_ = stack[5].m_obj;
lean_object* v___y_4117_ = stack[6].m_obj;
lean_object* v_res_4120_;
v_res_4120_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0(v_x_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
stack->m_obj
 = v_res_4120_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0___boxed(lean_object* v_x_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0(v_x_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
return v_res_4129_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(lean_object* v_lctx_4130_, lean_object* v_localInsts_4131_, lean_object* v_x_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v___f_4140_; lean_object* v___x_4141_; 
lean_inc(v___y_4134_);
lean_inc_ref(v___y_4133_);
v___f_4140_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4140_, 0, v_x_4132_);
lean_closure_set(v___f_4140_, 1, v___y_4133_);
lean_closure_set(v___f_4140_, 2, v___y_4134_);
v___x_4141_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4130_, v_localInsts_4131_, v___f_4140_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
if (lean_obj_tag(v___x_4141_) == 0)
{
return v___x_4141_;
}
else
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4149_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4144_ = v___x_4141_;
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___x_4141_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4147_; 
if (v_isShared_4145_ == 0)
{
v___x_4147_ = v___x_4144_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_4130_ = stack[0].m_obj;
lean_object* v_localInsts_4131_ = stack[1].m_obj;
lean_object* v_x_4132_ = stack[2].m_obj;
lean_object* v___y_4133_ = stack[3].m_obj;
lean_object* v___y_4134_ = stack[4].m_obj;
lean_object* v___y_4135_ = stack[5].m_obj;
lean_object* v___y_4136_ = stack[6].m_obj;
lean_object* v___y_4137_ = stack[7].m_obj;
lean_object* v___y_4138_ = stack[8].m_obj;
lean_object* v_res_4150_;
v_res_4150_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(v_lctx_4130_, v_localInsts_4131_, v_x_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
stack->m_obj
 = v_res_4150_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___boxed(lean_object* v_lctx_4151_, lean_object* v_localInsts_4152_, lean_object* v_x_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_){
_start:
{
lean_object* v_res_4161_; 
v_res_4161_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(v_lctx_4151_, v_localInsts_4152_, v_x_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
lean_dec(v___y_4159_);
lean_dec_ref(v___y_4158_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
return v_res_4161_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0(lean_object* v_00_u03b1_4162_, lean_object* v_lctx_4163_, lean_object* v_localInsts_4164_, lean_object* v_x_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v___x_4173_; 
v___x_4173_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(v_lctx_4163_, v_localInsts_4164_, v_x_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
return v___x_4173_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_4163_ = stack[1].m_obj;
lean_object* v_localInsts_4164_ = stack[2].m_obj;
lean_object* v_x_4165_ = stack[3].m_obj;
lean_object* v___y_4166_ = stack[4].m_obj;
lean_object* v___y_4167_ = stack[5].m_obj;
lean_object* v___y_4168_ = stack[6].m_obj;
lean_object* v___y_4169_ = stack[7].m_obj;
lean_object* v___y_4170_ = stack[8].m_obj;
lean_object* v___y_4171_ = stack[9].m_obj;
lean_object* v_res_4174_;
v_res_4174_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0(lean_box(0), v_lctx_4163_, v_localInsts_4164_, v_x_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
stack->m_obj
 = v_res_4174_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___boxed(lean_object* v_00_u03b1_4175_, lean_object* v_lctx_4176_, lean_object* v_localInsts_4177_, lean_object* v_x_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0(v_00_u03b1_4175_, v_lctx_4176_, v_localInsts_4177_, v_x_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
lean_dec(v___y_4182_);
lean_dec_ref(v___y_4181_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4179_);
return v_res_4186_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0(lean_object* v_k_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v___x_4195_; 
lean_inc(v___y_4189_);
lean_inc_ref(v___y_4188_);
v___x_4195_ = lean_apply_7(v_k_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, lean_box(0));
return v___x_4195_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_4187_ = stack[0].m_obj;
lean_object* v___y_4188_ = stack[1].m_obj;
lean_object* v___y_4189_ = stack[2].m_obj;
lean_object* v___y_4190_ = stack[3].m_obj;
lean_object* v___y_4191_ = stack[4].m_obj;
lean_object* v___y_4192_ = stack[5].m_obj;
lean_object* v___y_4193_ = stack[6].m_obj;
lean_object* v_res_4196_;
v_res_4196_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0(v_k_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
stack->m_obj
 = v_res_4196_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0___boxed(lean_object* v_k_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0(v_k_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
return v_res_4205_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg(lean_object* v_k_4206_, uint8_t v_allowLevelAssignments_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
lean_object* v___f_4215_; lean_object* v___x_4216_; 
lean_inc(v___y_4209_);
lean_inc_ref(v___y_4208_);
v___f_4215_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4215_, 0, v_k_4206_);
lean_closure_set(v___f_4215_, 1, v___y_4208_);
lean_closure_set(v___f_4215_, 2, v___y_4209_);
v___x_4216_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_4207_, v___f_4215_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
if (lean_obj_tag(v___x_4216_) == 0)
{
return v___x_4216_;
}
else
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4219_ = v___x_4216_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4216_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4222_; 
if (v_isShared_4220_ == 0)
{
v___x_4222_ = v___x_4219_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_a_4217_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_4206_ = stack[0].m_obj;
uint8_t v_allowLevelAssignments_4207_ = stack[1].m_num;
lean_object* v___y_4208_ = stack[2].m_obj;
lean_object* v___y_4209_ = stack[3].m_obj;
lean_object* v___y_4210_ = stack[4].m_obj;
lean_object* v___y_4211_ = stack[5].m_obj;
lean_object* v___y_4212_ = stack[6].m_obj;
lean_object* v___y_4213_ = stack[7].m_obj;
lean_object* v_res_4225_;
v_res_4225_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg(v_k_4206_, v_allowLevelAssignments_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
stack->m_obj
 = v_res_4225_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___boxed(lean_object* v_k_4226_, lean_object* v_allowLevelAssignments_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_4235_; lean_object* v_res_4236_; 
v_allowLevelAssignments_boxed_4235_ = lean_unbox(v_allowLevelAssignments_4227_);
v_res_4236_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg(v_k_4226_, v_allowLevelAssignments_boxed_4235_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
return v_res_4236_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1(lean_object* v_00_u03b1_4237_, lean_object* v_k_4238_, uint8_t v_allowLevelAssignments_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_){
_start:
{
lean_object* v___x_4247_; 
v___x_4247_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg(v_k_4238_, v_allowLevelAssignments_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
return v___x_4247_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_4238_ = stack[1].m_obj;
uint8_t v_allowLevelAssignments_4239_ = stack[2].m_num;
lean_object* v___y_4240_ = stack[3].m_obj;
lean_object* v___y_4241_ = stack[4].m_obj;
lean_object* v___y_4242_ = stack[5].m_obj;
lean_object* v___y_4243_ = stack[6].m_obj;
lean_object* v___y_4244_ = stack[7].m_obj;
lean_object* v___y_4245_ = stack[8].m_obj;
lean_object* v_res_4248_;
v_res_4248_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1(lean_box(0), v_k_4238_, v_allowLevelAssignments_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
stack->m_obj
 = v_res_4248_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___boxed(lean_object* v_00_u03b1_4249_, lean_object* v_k_4250_, lean_object* v_allowLevelAssignments_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_4259_; lean_object* v_res_4260_; 
v_allowLevelAssignments_boxed_4259_ = lean_unbox(v_allowLevelAssignments_4251_);
v_res_4260_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1(v_00_u03b1_4249_, v_k_4250_, v_allowLevelAssignments_boxed_4259_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4254_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__0(lean_object* v_cfg_4261_){
_start:
{
uint8_t v_foApprox_4262_; uint8_t v_ctxApprox_4263_; uint8_t v_quasiPatternApprox_4264_; uint8_t v_constApprox_4265_; uint8_t v_isDefEqStuckEx_4266_; uint8_t v_unificationHints_4267_; uint8_t v_proofIrrelevance_4268_; uint8_t v_assignSyntheticOpaque_4269_; uint8_t v_offsetCnstrs_4270_; uint8_t v_transparency_4271_; uint8_t v_univApprox_4272_; uint8_t v_zetaUnused_4273_; uint8_t v_canUnfoldPredicateConfig_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4284_; 
v_foApprox_4262_ = lean_ctor_get_uint8(v_cfg_4261_, 0);
v_ctxApprox_4263_ = lean_ctor_get_uint8(v_cfg_4261_, 1);
v_quasiPatternApprox_4264_ = lean_ctor_get_uint8(v_cfg_4261_, 2);
v_constApprox_4265_ = lean_ctor_get_uint8(v_cfg_4261_, 3);
v_isDefEqStuckEx_4266_ = lean_ctor_get_uint8(v_cfg_4261_, 4);
v_unificationHints_4267_ = lean_ctor_get_uint8(v_cfg_4261_, 5);
v_proofIrrelevance_4268_ = lean_ctor_get_uint8(v_cfg_4261_, 6);
v_assignSyntheticOpaque_4269_ = lean_ctor_get_uint8(v_cfg_4261_, 7);
v_offsetCnstrs_4270_ = lean_ctor_get_uint8(v_cfg_4261_, 8);
v_transparency_4271_ = lean_ctor_get_uint8(v_cfg_4261_, 9);
v_univApprox_4272_ = lean_ctor_get_uint8(v_cfg_4261_, 11);
v_zetaUnused_4273_ = lean_ctor_get_uint8(v_cfg_4261_, 17);
v_canUnfoldPredicateConfig_4274_ = lean_ctor_get_uint8(v_cfg_4261_, 19);
v_isSharedCheck_4284_ = !lean_is_exclusive(v_cfg_4261_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4276_ = v_cfg_4261_;
v_isShared_4277_ = v_isSharedCheck_4284_;
goto v_resetjp_4275_;
}
else
{
lean_dec(v_cfg_4261_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4284_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
uint8_t v___x_4278_; uint8_t v___x_4279_; uint8_t v___x_4280_; lean_object* v___x_4282_; 
v___x_4278_ = 0;
v___x_4279_ = 1;
v___x_4280_ = 2;
if (v_isShared_4277_ == 0)
{
v___x_4282_ = v___x_4276_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4283_, 0, v_foApprox_4262_);
lean_ctor_set_uint8(v_reuseFailAlloc_4283_, 1, v_ctxApprox_4263_);
lean_ctor_set_uint8(v_reuseFailAlloc_4283_, 2, v_quasiPatternApprox_4264_);
lean_ctor_set_uint8(v_reuseFailAlloc_4283_, 3, v_constApprox_4265_);
lean_ctor_set_uint8(v_reuseFailAlloc_4283_, 4, v_isDefEqStuckEx_4266_);
lean_ctor_set_uint8(v_reuseFailAlloc_4283_, 5, v_unificationHints_4267_);
lean_ctor_set_uint8(v_reuseFailAlloc_4283_, 6, v_proofIrrelevance_4268_);
lean_ctor_set_uint8(v_reuseFailAlloc_4283_, 7, v_assignSyntheticOpaque_4269_);
lean_ctor_set_uint8(v_reuseFailAlloc_4283_, 8, v_offsetCnstrs_4270_);
lean_ctor_set_uint8(v_reuseFailAlloc_4283_, 9, v_transparency_4271_);
lean_ctor_set_uint8(v_reuseFailAlloc_4283_, 11, v_univApprox_4272_);
lean_ctor_set_uint8(v_reuseFailAlloc_4283_, 17, v_zetaUnused_4273_);
lean_ctor_set_uint8(v_reuseFailAlloc_4283_, 19, v_canUnfoldPredicateConfig_4274_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
lean_ctor_set_uint8(v___x_4282_, 10, v___x_4278_);
lean_ctor_set_uint8(v___x_4282_, 12, v___x_4279_);
lean_ctor_set_uint8(v___x_4282_, 13, v___x_4279_);
lean_ctor_set_uint8(v___x_4282_, 14, v___x_4280_);
lean_ctor_set_uint8(v___x_4282_, 15, v___x_4279_);
lean_ctor_set_uint8(v___x_4282_, 16, v___x_4279_);
lean_ctor_set_uint8(v___x_4282_, 18, v___x_4279_);
return v___x_4282_;
}
}
}
}
lean_object* l_Lean_Meta_Sym_letToHave___lam__1(lean_object* v___x_4285_, lean_object* v_e_4286_, lean_object* v___x_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
lean_object* v___x_4295_; lean_object* v_a_4297_; lean_object* v___x_4300_; 
v___x_4295_ = lean_st_mk_ref(v___x_4285_);
lean_inc_ref(v_e_4286_);
v___x_4300_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_e_4286_, v___x_4287_, v___x_4295_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v_a_4301_; uint8_t v___x_4302_; 
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
lean_inc(v_a_4301_);
lean_dec_ref_known(v___x_4300_, 1);
v___x_4302_ = lean_unbox(v_a_4301_);
lean_dec(v_a_4301_);
if (v___x_4302_ == 0)
{
v_a_4297_ = v_e_4286_;
goto v___jp_4296_;
}
else
{
lean_object* v___x_4303_; 
v___x_4303_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_e_4286_, v___x_4287_, v___x_4295_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v_a_4304_; 
v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
lean_inc(v_a_4304_);
lean_dec_ref_known(v___x_4303_, 1);
v_a_4297_ = v_a_4304_;
goto v___jp_4296_;
}
else
{
lean_dec(v___x_4295_);
return v___x_4303_;
}
}
}
else
{
lean_object* v_a_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4312_; 
lean_dec(v___x_4295_);
lean_dec_ref(v_e_4286_);
v_a_4305_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4307_ = v___x_4300_;
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_a_4305_);
lean_dec(v___x_4300_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4310_; 
if (v_isShared_4308_ == 0)
{
v___x_4310_ = v___x_4307_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4305_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
v___jp_4296_:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4298_ = lean_st_ref_get(v___x_4295_);
lean_dec(v___x_4295_);
lean_dec(v___x_4298_);
v___x_4299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4299_, 0, v_a_4297_);
return v___x_4299_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_letToHave___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4285_ = stack[0].m_obj;
lean_object* v_e_4286_ = stack[1].m_obj;
lean_object* v___x_4287_ = stack[2].m_obj;
lean_object* v___y_4288_ = stack[3].m_obj;
lean_object* v___y_4289_ = stack[4].m_obj;
lean_object* v___y_4290_ = stack[5].m_obj;
lean_object* v___y_4291_ = stack[6].m_obj;
lean_object* v___y_4292_ = stack[7].m_obj;
lean_object* v___y_4293_ = stack[8].m_obj;
lean_object* v_res_4313_;
v_res_4313_ = l_Lean_Meta_Sym_letToHave___lam__1(v___x_4285_, v_e_4286_, v___x_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_);
stack->m_obj
 = v_res_4313_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__1___boxed(lean_object* v___x_4314_, lean_object* v_e_4315_, lean_object* v___x_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_){
_start:
{
lean_object* v_res_4324_; 
v_res_4324_ = l_Lean_Meta_Sym_letToHave___lam__1(v___x_4314_, v_e_4315_, v___x_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
lean_dec(v___y_4320_);
lean_dec_ref(v___y_4319_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
lean_dec_ref(v___x_4316_);
return v_res_4324_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___lam__2___closed__0(void){
_start:
{
lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4325_ = lean_unsigned_to_nat(0u);
v___x_4326_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1);
v___x_4327_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4326_);
lean_ctor_set(v___x_4327_, 1, v___x_4326_);
lean_ctor_set(v___x_4327_, 2, v___x_4326_);
lean_ctor_set(v___x_4327_, 3, v___x_4326_);
lean_ctor_set(v___x_4327_, 4, v___x_4326_);
lean_ctor_set(v___x_4327_, 5, v___x_4325_);
return v___x_4327_;
}
}
lean_object* l_Lean_Meta_Sym_letToHave___lam__2(lean_object* v_e_4328_, lean_object* v_____do__lift_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_){
_start:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___f_4340_; lean_object* v___x_4341_; 
v___x_4337_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___closed__0));
v___x_4338_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2);
v___x_4339_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__2___closed__0, &l_Lean_Meta_Sym_letToHave___lam__2___closed__0_once, _init_l_Lean_Meta_Sym_letToHave___lam__2___closed__0);
v___f_4340_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_letToHave___lam__1___boxed), 10, 3);
lean_closure_set(v___f_4340_, 0, v___x_4339_);
lean_closure_set(v___f_4340_, 1, v_e_4328_);
lean_closure_set(v___f_4340_, 2, v___x_4338_);
v___x_4341_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(v_____do__lift_4329_, v___x_4337_, v___f_4340_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_);
return v___x_4341_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_letToHave___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4328_ = stack[0].m_obj;
lean_object* v_____do__lift_4329_ = stack[1].m_obj;
lean_object* v___y_4330_ = stack[2].m_obj;
lean_object* v___y_4331_ = stack[3].m_obj;
lean_object* v___y_4332_ = stack[4].m_obj;
lean_object* v___y_4333_ = stack[5].m_obj;
lean_object* v___y_4334_ = stack[6].m_obj;
lean_object* v___y_4335_ = stack[7].m_obj;
lean_object* v_res_4342_;
v_res_4342_ = l_Lean_Meta_Sym_letToHave___lam__2(v_e_4328_, v_____do__lift_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_);
stack->m_obj
 = v_res_4342_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__2___boxed(lean_object* v_e_4343_, lean_object* v_____do__lift_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l_Lean_Meta_Sym_letToHave___lam__2(v_e_4343_, v_____do__lift_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
lean_dec(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
return v_res_4352_;
}
}
lean_object* l_Lean_Meta_Sym_letToHave___lam__3(lean_object* v___y_4353_, lean_object* v_cache_4354_, lean_object* v_a_x3f_4355_){
_start:
{
lean_object* v___x_4357_; lean_object* v_mctx_4358_; lean_object* v_zetaDeltaFVarIds_4359_; lean_object* v_postponed_4360_; lean_object* v_diag_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4371_; 
v___x_4357_ = lean_st_ref_take(v___y_4353_);
v_mctx_4358_ = lean_ctor_get(v___x_4357_, 0);
v_zetaDeltaFVarIds_4359_ = lean_ctor_get(v___x_4357_, 2);
v_postponed_4360_ = lean_ctor_get(v___x_4357_, 3);
v_diag_4361_ = lean_ctor_get(v___x_4357_, 4);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4371_ == 0)
{
lean_object* v_unused_4372_; 
v_unused_4372_ = lean_ctor_get(v___x_4357_, 1);
lean_dec(v_unused_4372_);
v___x_4363_ = v___x_4357_;
v_isShared_4364_ = v_isSharedCheck_4371_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_diag_4361_);
lean_inc(v_postponed_4360_);
lean_inc(v_zetaDeltaFVarIds_4359_);
lean_inc(v_mctx_4358_);
lean_dec(v___x_4357_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4371_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v___x_4365_; lean_object* v___x_4367_; 
v___x_4365_ = lean_box(0);
if (v_isShared_4364_ == 0)
{
lean_ctor_set(v___x_4363_, 1, v_cache_4354_);
v___x_4367_ = v___x_4363_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_mctx_4358_);
lean_ctor_set(v_reuseFailAlloc_4370_, 1, v_cache_4354_);
lean_ctor_set(v_reuseFailAlloc_4370_, 2, v_zetaDeltaFVarIds_4359_);
lean_ctor_set(v_reuseFailAlloc_4370_, 3, v_postponed_4360_);
lean_ctor_set(v_reuseFailAlloc_4370_, 4, v_diag_4361_);
v___x_4367_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___x_4368_ = lean_st_ref_put(v___y_4353_, v___x_4367_);
v___x_4369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4369_, 0, v___x_4365_);
return v___x_4369_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_letToHave___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4353_ = stack[0].m_obj;
lean_object* v_cache_4354_ = stack[1].m_obj;
lean_object* v_a_x3f_4355_ = stack[2].m_obj;
lean_object* v_res_4373_;
v_res_4373_ = l_Lean_Meta_Sym_letToHave___lam__3(v___y_4353_, v_cache_4354_, v_a_x3f_4355_);
stack->m_obj
 = v_res_4373_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__3___boxed(lean_object* v___y_4374_, lean_object* v_cache_4375_, lean_object* v_a_x3f_4376_, lean_object* v___y_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l_Lean_Meta_Sym_letToHave___lam__3(v___y_4374_, v_cache_4375_, v_a_x3f_4376_);
lean_dec(v_a_x3f_4376_);
lean_dec(v___y_4374_);
return v_res_4378_;
}
}
lean_object* l_Lean_Meta_Sym_letToHave___lam__4(lean_object* v___y_4379_, lean_object* v_zetaDeltaFVarIds_4380_, lean_object* v_a_x3f_4381_){
_start:
{
lean_object* v___x_4383_; lean_object* v_mctx_4384_; lean_object* v_cache_4385_; lean_object* v_postponed_4386_; lean_object* v_diag_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4397_; 
v___x_4383_ = lean_st_ref_take(v___y_4379_);
v_mctx_4384_ = lean_ctor_get(v___x_4383_, 0);
v_cache_4385_ = lean_ctor_get(v___x_4383_, 1);
v_postponed_4386_ = lean_ctor_get(v___x_4383_, 3);
v_diag_4387_ = lean_ctor_get(v___x_4383_, 4);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4397_ == 0)
{
lean_object* v_unused_4398_; 
v_unused_4398_ = lean_ctor_get(v___x_4383_, 2);
lean_dec(v_unused_4398_);
v___x_4389_ = v___x_4383_;
v_isShared_4390_ = v_isSharedCheck_4397_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_diag_4387_);
lean_inc(v_postponed_4386_);
lean_inc(v_cache_4385_);
lean_inc(v_mctx_4384_);
lean_dec(v___x_4383_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4397_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v___x_4391_; lean_object* v___x_4393_; 
v___x_4391_ = lean_box(0);
if (v_isShared_4390_ == 0)
{
lean_ctor_set(v___x_4389_, 2, v_zetaDeltaFVarIds_4380_);
v___x_4393_ = v___x_4389_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_mctx_4384_);
lean_ctor_set(v_reuseFailAlloc_4396_, 1, v_cache_4385_);
lean_ctor_set(v_reuseFailAlloc_4396_, 2, v_zetaDeltaFVarIds_4380_);
lean_ctor_set(v_reuseFailAlloc_4396_, 3, v_postponed_4386_);
lean_ctor_set(v_reuseFailAlloc_4396_, 4, v_diag_4387_);
v___x_4393_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; 
v___x_4394_ = lean_st_ref_put(v___y_4379_, v___x_4393_);
v___x_4395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4391_);
return v___x_4395_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_letToHave___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4379_ = stack[0].m_obj;
lean_object* v_zetaDeltaFVarIds_4380_ = stack[1].m_obj;
lean_object* v_a_x3f_4381_ = stack[2].m_obj;
lean_object* v_res_4399_;
v_res_4399_ = l_Lean_Meta_Sym_letToHave___lam__4(v___y_4379_, v_zetaDeltaFVarIds_4380_, v_a_x3f_4381_);
stack->m_obj
 = v_res_4399_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__4___boxed(lean_object* v___y_4400_, lean_object* v_zetaDeltaFVarIds_4401_, lean_object* v_a_x3f_4402_, lean_object* v___y_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l_Lean_Meta_Sym_letToHave___lam__4(v___y_4400_, v_zetaDeltaFVarIds_4401_, v_a_x3f_4402_);
lean_dec(v_a_x3f_4402_);
lean_dec(v___y_4400_);
return v_res_4404_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__0(void){
_start:
{
lean_object* v___x_4405_; 
v___x_4405_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4405_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__1(void){
_start:
{
lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4406_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__5___closed__0, &l_Lean_Meta_Sym_letToHave___lam__5___closed__0_once, _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__0);
v___x_4407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4407_, 0, v___x_4406_);
return v___x_4407_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__2(void){
_start:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4408_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__5___closed__1, &l_Lean_Meta_Sym_letToHave___lam__5___closed__1_once, _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__1);
v___x_4409_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4408_);
lean_ctor_set(v___x_4409_, 1, v___x_4408_);
lean_ctor_set(v___x_4409_, 2, v___x_4408_);
lean_ctor_set(v___x_4409_, 3, v___x_4408_);
lean_ctor_set(v___x_4409_, 4, v___x_4408_);
lean_ctor_set(v___x_4409_, 5, v___x_4408_);
return v___x_4409_;
}
}
lean_object* l_Lean_Meta_Sym_letToHave___lam__5(uint8_t v___x_4410_, lean_object* v___f_4411_, lean_object* v___f_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v_cache_4422_; lean_object* v_a_4424_; lean_object* v___x_4435_; lean_object* v_mctx_4436_; lean_object* v_zetaDeltaFVarIds_4437_; lean_object* v_postponed_4438_; lean_object* v_diag_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4511_; 
v___x_4420_ = lean_box(1);
v___x_4421_ = lean_st_ref_get(v___y_4416_);
v_cache_4422_ = lean_ctor_get(v___x_4421_, 1);
lean_inc_ref(v_cache_4422_);
lean_dec(v___x_4421_);
v___x_4435_ = lean_st_ref_take(v___y_4416_);
v_mctx_4436_ = lean_ctor_get(v___x_4435_, 0);
v_zetaDeltaFVarIds_4437_ = lean_ctor_get(v___x_4435_, 2);
v_postponed_4438_ = lean_ctor_get(v___x_4435_, 3);
v_diag_4439_ = lean_ctor_get(v___x_4435_, 4);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4511_ == 0)
{
lean_object* v_unused_4512_; 
v_unused_4512_ = lean_ctor_get(v___x_4435_, 1);
lean_dec(v_unused_4512_);
v___x_4441_ = v___x_4435_;
v_isShared_4442_ = v_isSharedCheck_4511_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_diag_4439_);
lean_inc(v_postponed_4438_);
lean_inc(v_zetaDeltaFVarIds_4437_);
lean_inc(v_mctx_4436_);
lean_dec(v___x_4435_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4511_;
goto v_resetjp_4440_;
}
v___jp_4423_:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4433_; 
v___x_4425_ = lean_box(0);
v___x_4426_ = l_Lean_Meta_Sym_letToHave___lam__3(v___y_4416_, v_cache_4422_, v___x_4425_);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4433_ == 0)
{
lean_object* v_unused_4434_; 
v_unused_4434_ = lean_ctor_get(v___x_4426_, 0);
lean_dec(v_unused_4434_);
v___x_4428_ = v___x_4426_;
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
else
{
lean_dec(v___x_4426_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4431_; 
if (v_isShared_4429_ == 0)
{
lean_ctor_set_tag(v___x_4428_, 1);
lean_ctor_set(v___x_4428_, 0, v_a_4424_);
v___x_4431_ = v___x_4428_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4424_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
}
v_resetjp_4440_:
{
lean_object* v___x_4443_; lean_object* v___x_4445_; 
v___x_4443_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__5___closed__2, &l_Lean_Meta_Sym_letToHave___lam__5___closed__2_once, _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__2);
if (v_isShared_4442_ == 0)
{
lean_ctor_set(v___x_4441_, 1, v___x_4443_);
v___x_4445_ = v___x_4441_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_mctx_4436_);
lean_ctor_set(v_reuseFailAlloc_4510_, 1, v___x_4443_);
lean_ctor_set(v_reuseFailAlloc_4510_, 2, v_zetaDeltaFVarIds_4437_);
lean_ctor_set(v_reuseFailAlloc_4510_, 3, v_postponed_4438_);
lean_ctor_set(v_reuseFailAlloc_4510_, 4, v_diag_4439_);
v___x_4445_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
lean_object* v___x_4446_; lean_object* v_keyedConfig_4447_; lean_object* v_zetaDeltaSet_4448_; lean_object* v_lctx_4449_; lean_object* v_localInstances_4450_; lean_object* v_defEqCtx_x3f_4451_; lean_object* v_synthPendingDepth_4452_; lean_object* v_customCanUnfoldPredicate_x3f_4453_; uint8_t v_univApprox_4454_; uint8_t v_inTypeClassResolution_4455_; uint8_t v_cacheInferType_4456_; uint8_t v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v_mctx_4460_; lean_object* v_cache_4461_; lean_object* v_zetaDeltaFVarIds_4462_; lean_object* v_postponed_4463_; lean_object* v_diag_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4509_; 
v___x_4446_ = lean_st_ref_put(v___y_4416_, v___x_4445_);
v_keyedConfig_4447_ = lean_ctor_get(v___y_4415_, 0);
v_zetaDeltaSet_4448_ = lean_ctor_get(v___y_4415_, 1);
v_lctx_4449_ = lean_ctor_get(v___y_4415_, 2);
v_localInstances_4450_ = lean_ctor_get(v___y_4415_, 3);
v_defEqCtx_x3f_4451_ = lean_ctor_get(v___y_4415_, 4);
v_synthPendingDepth_4452_ = lean_ctor_get(v___y_4415_, 5);
v_customCanUnfoldPredicate_x3f_4453_ = lean_ctor_get(v___y_4415_, 6);
v_univApprox_4454_ = lean_ctor_get_uint8(v___y_4415_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4455_ = lean_ctor_get_uint8(v___y_4415_, sizeof(void*)*7 + 2);
v_cacheInferType_4456_ = lean_ctor_get_uint8(v___y_4415_, sizeof(void*)*7 + 3);
v___x_4457_ = 1;
lean_inc(v_customCanUnfoldPredicate_x3f_4453_);
lean_inc(v_synthPendingDepth_4452_);
lean_inc(v_defEqCtx_x3f_4451_);
lean_inc_ref(v_localInstances_4450_);
lean_inc_ref(v_lctx_4449_);
lean_inc(v_zetaDeltaSet_4448_);
lean_inc_ref(v_keyedConfig_4447_);
v___x_4458_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4458_, 0, v_keyedConfig_4447_);
lean_ctor_set(v___x_4458_, 1, v_zetaDeltaSet_4448_);
lean_ctor_set(v___x_4458_, 2, v_lctx_4449_);
lean_ctor_set(v___x_4458_, 3, v_localInstances_4450_);
lean_ctor_set(v___x_4458_, 4, v_defEqCtx_x3f_4451_);
lean_ctor_set(v___x_4458_, 5, v_synthPendingDepth_4452_);
lean_ctor_set(v___x_4458_, 6, v_customCanUnfoldPredicate_x3f_4453_);
lean_ctor_set_uint8(v___x_4458_, sizeof(void*)*7, v___x_4457_);
lean_ctor_set_uint8(v___x_4458_, sizeof(void*)*7 + 1, v_univApprox_4454_);
lean_ctor_set_uint8(v___x_4458_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4455_);
lean_ctor_set_uint8(v___x_4458_, sizeof(void*)*7 + 3, v_cacheInferType_4456_);
v___x_4459_ = lean_st_ref_take(v___y_4416_);
v_mctx_4460_ = lean_ctor_get(v___x_4459_, 0);
v_cache_4461_ = lean_ctor_get(v___x_4459_, 1);
v_zetaDeltaFVarIds_4462_ = lean_ctor_get(v___x_4459_, 2);
v_postponed_4463_ = lean_ctor_get(v___x_4459_, 3);
v_diag_4464_ = lean_ctor_get(v___x_4459_, 4);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4466_ = v___x_4459_;
v_isShared_4467_ = v_isSharedCheck_4509_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_diag_4464_);
lean_inc(v_postponed_4463_);
lean_inc(v_zetaDeltaFVarIds_4462_);
lean_inc(v_cache_4461_);
lean_inc(v_mctx_4460_);
lean_dec(v___x_4459_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4509_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
lean_object* v_a_4469_; lean_object* v_a_4473_; lean_object* v___x_4486_; 
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 2, v___x_4420_);
v___x_4486_ = v___x_4466_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_mctx_4460_);
lean_ctor_set(v_reuseFailAlloc_4508_, 1, v_cache_4461_);
lean_ctor_set(v_reuseFailAlloc_4508_, 2, v___x_4420_);
lean_ctor_set(v_reuseFailAlloc_4508_, 3, v_postponed_4463_);
lean_ctor_set(v_reuseFailAlloc_4508_, 4, v_diag_4464_);
v___x_4486_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4485_;
}
v___jp_4468_:
{
lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4470_ = lean_box(0);
v___x_4471_ = l_Lean_Meta_Sym_letToHave___lam__4(v___y_4416_, v_zetaDeltaFVarIds_4462_, v___x_4470_);
lean_dec_ref(v___x_4471_);
v_a_4424_ = v_a_4469_;
goto v___jp_4423_;
}
v___jp_4472_:
{
lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4483_; 
lean_inc(v_a_4473_);
v___x_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4474_, 0, v_a_4473_);
v___x_4475_ = l_Lean_Meta_Sym_letToHave___lam__4(v___y_4416_, v_zetaDeltaFVarIds_4462_, v___x_4474_);
lean_dec_ref(v___x_4475_);
v___x_4476_ = l_Lean_Meta_Sym_letToHave___lam__3(v___y_4416_, v_cache_4422_, v___x_4474_);
lean_dec_ref_known(v___x_4474_, 1);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4483_ == 0)
{
lean_object* v_unused_4484_; 
v_unused_4484_ = lean_ctor_get(v___x_4476_, 0);
lean_dec(v_unused_4484_);
v___x_4478_ = v___x_4476_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_dec(v___x_4476_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4481_; 
if (v_isShared_4479_ == 0)
{
lean_ctor_set(v___x_4478_, 0, v_a_4473_);
v___x_4481_ = v___x_4478_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4473_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
v_reusejp_4485_:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; uint8_t v_transparency_4489_; uint8_t v___x_4490_; 
v___x_4487_ = lean_st_ref_put(v___y_4416_, v___x_4486_);
v___x_4488_ = l_Lean_Meta_Context_config(v___x_4458_);
lean_dec_ref_known(v___x_4458_, 7);
v_transparency_4489_ = lean_ctor_get_uint8(v___x_4488_, 9);
v___x_4490_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4489_, v___x_4410_);
if (v___x_4490_ == 0)
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; uint64_t v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
lean_dec_ref(v___x_4488_);
lean_inc_ref(v_keyedConfig_4447_);
v___x_4491_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4410_, v_keyedConfig_4447_);
lean_inc_n(v_customCanUnfoldPredicate_x3f_4453_, 2);
lean_inc_n(v_synthPendingDepth_4452_, 2);
lean_inc_n(v_defEqCtx_x3f_4451_, 2);
lean_inc_ref_n(v_localInstances_4450_, 2);
lean_inc_ref_n(v_lctx_4449_, 3);
lean_inc_n(v_zetaDeltaSet_4448_, 2);
v___x_4492_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4492_, 0, v___x_4491_);
lean_ctor_set(v___x_4492_, 1, v_zetaDeltaSet_4448_);
lean_ctor_set(v___x_4492_, 2, v_lctx_4449_);
lean_ctor_set(v___x_4492_, 3, v_localInstances_4450_);
lean_ctor_set(v___x_4492_, 4, v_defEqCtx_x3f_4451_);
lean_ctor_set(v___x_4492_, 5, v_synthPendingDepth_4452_);
lean_ctor_set(v___x_4492_, 6, v_customCanUnfoldPredicate_x3f_4453_);
lean_ctor_set_uint8(v___x_4492_, sizeof(void*)*7, v___x_4457_);
lean_ctor_set_uint8(v___x_4492_, sizeof(void*)*7 + 1, v_univApprox_4454_);
lean_ctor_set_uint8(v___x_4492_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4455_);
lean_ctor_set_uint8(v___x_4492_, sizeof(void*)*7 + 3, v_cacheInferType_4456_);
v___x_4493_ = l_Lean_Meta_Context_config(v___x_4492_);
lean_dec_ref_known(v___x_4492_, 7);
v___x_4494_ = lean_apply_1(v___f_4411_, v___x_4493_);
v___x_4495_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4494_);
v___x_4496_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4496_, 0, v___x_4494_);
lean_ctor_set_uint64(v___x_4496_, sizeof(void*)*1, v___x_4495_);
v___x_4497_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4497_, 0, v___x_4496_);
lean_ctor_set(v___x_4497_, 1, v_zetaDeltaSet_4448_);
lean_ctor_set(v___x_4497_, 2, v_lctx_4449_);
lean_ctor_set(v___x_4497_, 3, v_localInstances_4450_);
lean_ctor_set(v___x_4497_, 4, v_defEqCtx_x3f_4451_);
lean_ctor_set(v___x_4497_, 5, v_synthPendingDepth_4452_);
lean_ctor_set(v___x_4497_, 6, v_customCanUnfoldPredicate_x3f_4453_);
lean_ctor_set_uint8(v___x_4497_, sizeof(void*)*7, v___x_4457_);
lean_ctor_set_uint8(v___x_4497_, sizeof(void*)*7 + 1, v_univApprox_4454_);
lean_ctor_set_uint8(v___x_4497_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4455_);
lean_ctor_set_uint8(v___x_4497_, sizeof(void*)*7 + 3, v_cacheInferType_4456_);
lean_inc(v___y_4418_);
lean_inc_ref(v___y_4417_);
lean_inc(v___y_4416_);
lean_inc(v___y_4414_);
lean_inc_ref(v___y_4413_);
v___x_4498_ = lean_apply_8(v___f_4412_, v_lctx_4449_, v___y_4413_, v___y_4414_, v___x_4497_, v___y_4416_, v___y_4417_, v___y_4418_, lean_box(0));
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v_a_4499_; 
v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
lean_inc(v_a_4499_);
lean_dec_ref_known(v___x_4498_, 1);
v_a_4473_ = v_a_4499_;
goto v___jp_4472_;
}
else
{
lean_object* v_a_4500_; 
v_a_4500_ = lean_ctor_get(v___x_4498_, 0);
lean_inc(v_a_4500_);
lean_dec_ref_known(v___x_4498_, 1);
v_a_4469_ = v_a_4500_;
goto v___jp_4468_;
}
}
else
{
lean_object* v___x_4501_; uint64_t v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4501_ = lean_apply_1(v___f_4411_, v___x_4488_);
v___x_4502_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4501_);
v___x_4503_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4503_, 0, v___x_4501_);
lean_ctor_set_uint64(v___x_4503_, sizeof(void*)*1, v___x_4502_);
lean_inc(v_customCanUnfoldPredicate_x3f_4453_);
lean_inc(v_synthPendingDepth_4452_);
lean_inc(v_defEqCtx_x3f_4451_);
lean_inc_ref(v_localInstances_4450_);
lean_inc_ref_n(v_lctx_4449_, 2);
lean_inc(v_zetaDeltaSet_4448_);
v___x_4504_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4504_, 0, v___x_4503_);
lean_ctor_set(v___x_4504_, 1, v_zetaDeltaSet_4448_);
lean_ctor_set(v___x_4504_, 2, v_lctx_4449_);
lean_ctor_set(v___x_4504_, 3, v_localInstances_4450_);
lean_ctor_set(v___x_4504_, 4, v_defEqCtx_x3f_4451_);
lean_ctor_set(v___x_4504_, 5, v_synthPendingDepth_4452_);
lean_ctor_set(v___x_4504_, 6, v_customCanUnfoldPredicate_x3f_4453_);
lean_ctor_set_uint8(v___x_4504_, sizeof(void*)*7, v___x_4457_);
lean_ctor_set_uint8(v___x_4504_, sizeof(void*)*7 + 1, v_univApprox_4454_);
lean_ctor_set_uint8(v___x_4504_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4455_);
lean_ctor_set_uint8(v___x_4504_, sizeof(void*)*7 + 3, v_cacheInferType_4456_);
lean_inc(v___y_4418_);
lean_inc_ref(v___y_4417_);
lean_inc(v___y_4416_);
lean_inc(v___y_4414_);
lean_inc_ref(v___y_4413_);
v___x_4505_ = lean_apply_8(v___f_4412_, v_lctx_4449_, v___y_4413_, v___y_4414_, v___x_4504_, v___y_4416_, v___y_4417_, v___y_4418_, lean_box(0));
if (lean_obj_tag(v___x_4505_) == 0)
{
lean_object* v_a_4506_; 
v_a_4506_ = lean_ctor_get(v___x_4505_, 0);
lean_inc(v_a_4506_);
lean_dec_ref_known(v___x_4505_, 1);
v_a_4473_ = v_a_4506_;
goto v___jp_4472_;
}
else
{
lean_object* v_a_4507_; 
v_a_4507_ = lean_ctor_get(v___x_4505_, 0);
lean_inc(v_a_4507_);
lean_dec_ref_known(v___x_4505_, 1);
v_a_4469_ = v_a_4507_;
goto v___jp_4468_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_letToHave___lam__5_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_4410_ = stack[0].m_num;
lean_object* v___f_4411_ = stack[1].m_obj;
lean_object* v___f_4412_ = stack[2].m_obj;
lean_object* v___y_4413_ = stack[3].m_obj;
lean_object* v___y_4414_ = stack[4].m_obj;
lean_object* v___y_4415_ = stack[5].m_obj;
lean_object* v___y_4416_ = stack[6].m_obj;
lean_object* v___y_4417_ = stack[7].m_obj;
lean_object* v___y_4418_ = stack[8].m_obj;
lean_object* v_res_4513_;
v_res_4513_ = l_Lean_Meta_Sym_letToHave___lam__5(v___x_4410_, v___f_4411_, v___f_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
stack->m_obj
 = v_res_4513_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__5___boxed(lean_object* v___x_4514_, lean_object* v___f_4515_, lean_object* v___f_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
uint8_t v___x_18766__boxed_4524_; lean_object* v_res_4525_; 
v___x_18766__boxed_4524_ = lean_unbox(v___x_4514_);
v_res_4525_ = l_Lean_Meta_Sym_letToHave___lam__5(v___x_18766__boxed_4524_, v___f_4515_, v___f_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
return v_res_4525_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(lean_object* v_msg_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
lean_object* v_ref_4532_; lean_object* v___x_4533_; lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4542_; 
v_ref_4532_ = lean_ctor_get(v___y_4529_, 2);
v___x_4533_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(v_msg_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4542_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4536_ = v___x_4533_;
v_isShared_4537_ = v_isSharedCheck_4542_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4533_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4542_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4538_; lean_object* v___x_4540_; 
lean_inc(v_ref_4532_);
v___x_4538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4538_, 0, v_ref_4532_);
lean_ctor_set(v___x_4538_, 1, v_a_4534_);
if (v_isShared_4537_ == 0)
{
lean_ctor_set_tag(v___x_4536_, 1);
lean_ctor_set(v___x_4536_, 0, v___x_4538_);
v___x_4540_ = v___x_4536_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v___x_4538_);
v___x_4540_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
return v___x_4540_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4526_ = stack[0].m_obj;
lean_object* v___y_4527_ = stack[1].m_obj;
lean_object* v___y_4528_ = stack[2].m_obj;
lean_object* v___y_4529_ = stack[3].m_obj;
lean_object* v___y_4530_ = stack[4].m_obj;
lean_object* v_res_4543_;
v_res_4543_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(v_msg_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
stack->m_obj
 = v_res_4543_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg___boxed(lean_object* v_msg_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(v_msg_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
return v_res_4550_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(lean_object* v___y_4551_, uint8_t v_isExporting_4552_, lean_object* v___x_4553_, lean_object* v___y_4554_, lean_object* v___x_4555_, lean_object* v_a_x3f_4556_){
_start:
{
lean_object* v___x_4558_; lean_object* v_env_4559_; lean_object* v_nextMacroScope_4560_; lean_object* v_ngen_4561_; lean_object* v_auxDeclNGen_4562_; lean_object* v_traceState_4563_; lean_object* v_recordedDeps_4564_; lean_object* v_messages_4565_; lean_object* v_infoState_4566_; lean_object* v_snapshotTasks_4567_; lean_object* v___x_4569_; uint8_t v_isShared_4570_; uint8_t v_isSharedCheck_4592_; 
v___x_4558_ = lean_st_ref_take(v___y_4551_);
v_env_4559_ = lean_ctor_get(v___x_4558_, 0);
v_nextMacroScope_4560_ = lean_ctor_get(v___x_4558_, 1);
v_ngen_4561_ = lean_ctor_get(v___x_4558_, 2);
v_auxDeclNGen_4562_ = lean_ctor_get(v___x_4558_, 3);
v_traceState_4563_ = lean_ctor_get(v___x_4558_, 4);
v_recordedDeps_4564_ = lean_ctor_get(v___x_4558_, 6);
v_messages_4565_ = lean_ctor_get(v___x_4558_, 7);
v_infoState_4566_ = lean_ctor_get(v___x_4558_, 8);
v_snapshotTasks_4567_ = lean_ctor_get(v___x_4558_, 9);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4558_);
if (v_isSharedCheck_4592_ == 0)
{
lean_object* v_unused_4593_; 
v_unused_4593_ = lean_ctor_get(v___x_4558_, 5);
lean_dec(v_unused_4593_);
v___x_4569_ = v___x_4558_;
v_isShared_4570_ = v_isSharedCheck_4592_;
goto v_resetjp_4568_;
}
else
{
lean_inc(v_snapshotTasks_4567_);
lean_inc(v_infoState_4566_);
lean_inc(v_messages_4565_);
lean_inc(v_recordedDeps_4564_);
lean_inc(v_traceState_4563_);
lean_inc(v_auxDeclNGen_4562_);
lean_inc(v_ngen_4561_);
lean_inc(v_nextMacroScope_4560_);
lean_inc(v_env_4559_);
lean_dec(v___x_4558_);
v___x_4569_ = lean_box(0);
v_isShared_4570_ = v_isSharedCheck_4592_;
goto v_resetjp_4568_;
}
v_resetjp_4568_:
{
lean_object* v___x_4571_; lean_object* v___x_4573_; 
v___x_4571_ = l_Lean_Environment_setExporting(v_env_4559_, v_isExporting_4552_);
if (v_isShared_4570_ == 0)
{
lean_ctor_set(v___x_4569_, 5, v___x_4553_);
lean_ctor_set(v___x_4569_, 0, v___x_4571_);
v___x_4573_ = v___x_4569_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v___x_4571_);
lean_ctor_set(v_reuseFailAlloc_4591_, 1, v_nextMacroScope_4560_);
lean_ctor_set(v_reuseFailAlloc_4591_, 2, v_ngen_4561_);
lean_ctor_set(v_reuseFailAlloc_4591_, 3, v_auxDeclNGen_4562_);
lean_ctor_set(v_reuseFailAlloc_4591_, 4, v_traceState_4563_);
lean_ctor_set(v_reuseFailAlloc_4591_, 5, v___x_4553_);
lean_ctor_set(v_reuseFailAlloc_4591_, 6, v_recordedDeps_4564_);
lean_ctor_set(v_reuseFailAlloc_4591_, 7, v_messages_4565_);
lean_ctor_set(v_reuseFailAlloc_4591_, 8, v_infoState_4566_);
lean_ctor_set(v_reuseFailAlloc_4591_, 9, v_snapshotTasks_4567_);
v___x_4573_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v_mctx_4576_; lean_object* v_zetaDeltaFVarIds_4577_; lean_object* v_postponed_4578_; lean_object* v_diag_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4589_; 
v___x_4574_ = lean_st_ref_put(v___y_4551_, v___x_4573_);
v___x_4575_ = lean_st_ref_take(v___y_4554_);
v_mctx_4576_ = lean_ctor_get(v___x_4575_, 0);
v_zetaDeltaFVarIds_4577_ = lean_ctor_get(v___x_4575_, 2);
v_postponed_4578_ = lean_ctor_get(v___x_4575_, 3);
v_diag_4579_ = lean_ctor_get(v___x_4575_, 4);
v_isSharedCheck_4589_ = !lean_is_exclusive(v___x_4575_);
if (v_isSharedCheck_4589_ == 0)
{
lean_object* v_unused_4590_; 
v_unused_4590_ = lean_ctor_get(v___x_4575_, 1);
lean_dec(v_unused_4590_);
v___x_4581_ = v___x_4575_;
v_isShared_4582_ = v_isSharedCheck_4589_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_diag_4579_);
lean_inc(v_postponed_4578_);
lean_inc(v_zetaDeltaFVarIds_4577_);
lean_inc(v_mctx_4576_);
lean_dec(v___x_4575_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4589_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4583_; lean_object* v___x_4585_; 
v___x_4583_ = lean_box(0);
if (v_isShared_4582_ == 0)
{
lean_ctor_set(v___x_4581_, 1, v___x_4555_);
v___x_4585_ = v___x_4581_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v_mctx_4576_);
lean_ctor_set(v_reuseFailAlloc_4588_, 1, v___x_4555_);
lean_ctor_set(v_reuseFailAlloc_4588_, 2, v_zetaDeltaFVarIds_4577_);
lean_ctor_set(v_reuseFailAlloc_4588_, 3, v_postponed_4578_);
lean_ctor_set(v_reuseFailAlloc_4588_, 4, v_diag_4579_);
v___x_4585_ = v_reuseFailAlloc_4588_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
lean_object* v___x_4586_; lean_object* v___x_4587_; 
v___x_4586_ = lean_st_ref_put(v___y_4554_, v___x_4585_);
v___x_4587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4583_);
return v___x_4587_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4551_ = stack[0].m_obj;
uint8_t v_isExporting_4552_ = stack[1].m_num;
lean_object* v___x_4553_ = stack[2].m_obj;
lean_object* v___y_4554_ = stack[3].m_obj;
lean_object* v___x_4555_ = stack[4].m_obj;
lean_object* v_a_x3f_4556_ = stack[5].m_obj;
lean_object* v_res_4594_;
v_res_4594_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(v___y_4551_, v_isExporting_4552_, v___x_4553_, v___y_4554_, v___x_4555_, v_a_x3f_4556_);
stack->m_obj
 = v_res_4594_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_4595_, lean_object* v_isExporting_4596_, lean_object* v___x_4597_, lean_object* v___y_4598_, lean_object* v___x_4599_, lean_object* v_a_x3f_4600_, lean_object* v___y_4601_){
_start:
{
uint8_t v_isExporting_boxed_4602_; lean_object* v_res_4603_; 
v_isExporting_boxed_4602_ = lean_unbox(v_isExporting_4596_);
v_res_4603_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(v___y_4595_, v_isExporting_boxed_4602_, v___x_4597_, v___y_4598_, v___x_4599_, v_a_x3f_4600_);
lean_dec(v_a_x3f_4600_);
lean_dec(v___y_4598_);
lean_dec(v___y_4595_);
return v_res_4603_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4604_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__5___closed__0, &l_Lean_Meta_Sym_letToHave___lam__5___closed__0_once, _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__0);
v___x_4605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4605_, 0, v___x_4604_);
return v___x_4605_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4606_; lean_object* v___x_4607_; 
v___x_4606_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0);
v___x_4607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4607_, 0, v___x_4606_);
lean_ctor_set(v___x_4607_, 1, v___x_4606_);
return v___x_4607_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4608_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0);
v___x_4609_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4609_, 0, v___x_4608_);
lean_ctor_set(v___x_4609_, 1, v___x_4608_);
lean_ctor_set(v___x_4609_, 2, v___x_4608_);
lean_ctor_set(v___x_4609_, 3, v___x_4608_);
lean_ctor_set(v___x_4609_, 4, v___x_4608_);
lean_ctor_set(v___x_4609_, 5, v___x_4608_);
return v___x_4609_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(lean_object* v_x_4610_, uint8_t v_isExporting_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_){
_start:
{
lean_object* v___x_4619_; lean_object* v_env_4620_; lean_object* v___x_4621_; uint8_t v_isModule_4622_; 
v___x_4619_ = lean_st_ref_get(v___y_4617_);
v_env_4620_ = lean_ctor_get(v___x_4619_, 0);
lean_inc_ref(v_env_4620_);
lean_dec(v___x_4619_);
v___x_4621_ = l_Lean_Environment_header(v_env_4620_);
v_isModule_4622_ = lean_ctor_get_uint8(v___x_4621_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4621_);
if (v_isModule_4622_ == 0)
{
lean_object* v___x_4623_; 
lean_dec_ref(v_env_4620_);
lean_inc(v___y_4617_);
lean_inc_ref(v___y_4616_);
lean_inc(v___y_4615_);
lean_inc_ref(v___y_4614_);
lean_inc(v___y_4613_);
lean_inc_ref(v___y_4612_);
v___x_4623_ = lean_apply_7(v_x_4610_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, lean_box(0));
return v___x_4623_;
}
else
{
uint8_t v_isExporting_4624_; 
v_isExporting_4624_ = lean_ctor_get_uint8(v_env_4620_, sizeof(void*)*13);
lean_dec_ref(v_env_4620_);
if (v_isExporting_4611_ == 0)
{
if (v_isExporting_4624_ == 0)
{
lean_object* v___x_4691_; 
lean_inc(v___y_4617_);
lean_inc_ref(v___y_4616_);
lean_inc(v___y_4615_);
lean_inc_ref(v___y_4614_);
lean_inc(v___y_4613_);
lean_inc_ref(v___y_4612_);
v___x_4691_ = lean_apply_7(v_x_4610_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, lean_box(0));
return v___x_4691_;
}
else
{
goto v___jp_4625_;
}
}
else
{
if (v_isExporting_4624_ == 0)
{
goto v___jp_4625_;
}
else
{
lean_object* v___x_4692_; 
lean_inc(v___y_4617_);
lean_inc_ref(v___y_4616_);
lean_inc(v___y_4615_);
lean_inc_ref(v___y_4614_);
lean_inc(v___y_4613_);
lean_inc_ref(v___y_4612_);
v___x_4692_ = lean_apply_7(v_x_4610_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, lean_box(0));
return v___x_4692_;
}
}
v___jp_4625_:
{
lean_object* v___x_4626_; lean_object* v_env_4627_; lean_object* v_nextMacroScope_4628_; lean_object* v_ngen_4629_; lean_object* v_auxDeclNGen_4630_; lean_object* v_traceState_4631_; lean_object* v_recordedDeps_4632_; lean_object* v_messages_4633_; lean_object* v_infoState_4634_; lean_object* v_snapshotTasks_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4689_; 
v___x_4626_ = lean_st_ref_take(v___y_4617_);
v_env_4627_ = lean_ctor_get(v___x_4626_, 0);
v_nextMacroScope_4628_ = lean_ctor_get(v___x_4626_, 1);
v_ngen_4629_ = lean_ctor_get(v___x_4626_, 2);
v_auxDeclNGen_4630_ = lean_ctor_get(v___x_4626_, 3);
v_traceState_4631_ = lean_ctor_get(v___x_4626_, 4);
v_recordedDeps_4632_ = lean_ctor_get(v___x_4626_, 6);
v_messages_4633_ = lean_ctor_get(v___x_4626_, 7);
v_infoState_4634_ = lean_ctor_get(v___x_4626_, 8);
v_snapshotTasks_4635_ = lean_ctor_get(v___x_4626_, 9);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4689_ == 0)
{
lean_object* v_unused_4690_; 
v_unused_4690_ = lean_ctor_get(v___x_4626_, 5);
lean_dec(v_unused_4690_);
v___x_4637_ = v___x_4626_;
v_isShared_4638_ = v_isSharedCheck_4689_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_snapshotTasks_4635_);
lean_inc(v_infoState_4634_);
lean_inc(v_messages_4633_);
lean_inc(v_recordedDeps_4632_);
lean_inc(v_traceState_4631_);
lean_inc(v_auxDeclNGen_4630_);
lean_inc(v_ngen_4629_);
lean_inc(v_nextMacroScope_4628_);
lean_inc(v_env_4627_);
lean_dec(v___x_4626_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4689_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4642_; 
v___x_4639_ = l_Lean_Environment_setExporting(v_env_4627_, v_isExporting_4611_);
v___x_4640_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1);
if (v_isShared_4638_ == 0)
{
lean_ctor_set(v___x_4637_, 5, v___x_4640_);
lean_ctor_set(v___x_4637_, 0, v___x_4639_);
v___x_4642_ = v___x_4637_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v___x_4639_);
lean_ctor_set(v_reuseFailAlloc_4688_, 1, v_nextMacroScope_4628_);
lean_ctor_set(v_reuseFailAlloc_4688_, 2, v_ngen_4629_);
lean_ctor_set(v_reuseFailAlloc_4688_, 3, v_auxDeclNGen_4630_);
lean_ctor_set(v_reuseFailAlloc_4688_, 4, v_traceState_4631_);
lean_ctor_set(v_reuseFailAlloc_4688_, 5, v___x_4640_);
lean_ctor_set(v_reuseFailAlloc_4688_, 6, v_recordedDeps_4632_);
lean_ctor_set(v_reuseFailAlloc_4688_, 7, v_messages_4633_);
lean_ctor_set(v_reuseFailAlloc_4688_, 8, v_infoState_4634_);
lean_ctor_set(v_reuseFailAlloc_4688_, 9, v_snapshotTasks_4635_);
v___x_4642_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v_mctx_4645_; lean_object* v_zetaDeltaFVarIds_4646_; lean_object* v_postponed_4647_; lean_object* v_diag_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4686_; 
v___x_4643_ = lean_st_ref_put(v___y_4617_, v___x_4642_);
v___x_4644_ = lean_st_ref_take(v___y_4615_);
v_mctx_4645_ = lean_ctor_get(v___x_4644_, 0);
v_zetaDeltaFVarIds_4646_ = lean_ctor_get(v___x_4644_, 2);
v_postponed_4647_ = lean_ctor_get(v___x_4644_, 3);
v_diag_4648_ = lean_ctor_get(v___x_4644_, 4);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4644_);
if (v_isSharedCheck_4686_ == 0)
{
lean_object* v_unused_4687_; 
v_unused_4687_ = lean_ctor_get(v___x_4644_, 1);
lean_dec(v_unused_4687_);
v___x_4650_ = v___x_4644_;
v_isShared_4651_ = v_isSharedCheck_4686_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_diag_4648_);
lean_inc(v_postponed_4647_);
lean_inc(v_zetaDeltaFVarIds_4646_);
lean_inc(v_mctx_4645_);
lean_dec(v___x_4644_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4686_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v___x_4652_; lean_object* v___x_4654_; 
v___x_4652_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2);
if (v_isShared_4651_ == 0)
{
lean_ctor_set(v___x_4650_, 1, v___x_4652_);
v___x_4654_ = v___x_4650_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_mctx_4645_);
lean_ctor_set(v_reuseFailAlloc_4685_, 1, v___x_4652_);
lean_ctor_set(v_reuseFailAlloc_4685_, 2, v_zetaDeltaFVarIds_4646_);
lean_ctor_set(v_reuseFailAlloc_4685_, 3, v_postponed_4647_);
lean_ctor_set(v_reuseFailAlloc_4685_, 4, v_diag_4648_);
v___x_4654_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
lean_object* v___x_4655_; lean_object* v_r_4656_; 
v___x_4655_ = lean_st_ref_put(v___y_4615_, v___x_4654_);
lean_inc(v___y_4617_);
lean_inc_ref(v___y_4616_);
lean_inc(v___y_4615_);
lean_inc_ref(v___y_4614_);
lean_inc(v___y_4613_);
lean_inc_ref(v___y_4612_);
v_r_4656_ = lean_apply_7(v_x_4610_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, lean_box(0));
if (lean_obj_tag(v_r_4656_) == 0)
{
lean_object* v_a_4657_; lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4673_; 
v_a_4657_ = lean_ctor_get(v_r_4656_, 0);
v_isSharedCheck_4673_ = !lean_is_exclusive(v_r_4656_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4659_ = v_r_4656_;
v_isShared_4660_ = v_isSharedCheck_4673_;
goto v_resetjp_4658_;
}
else
{
lean_inc(v_a_4657_);
lean_dec(v_r_4656_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4673_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
lean_object* v___x_4662_; 
lean_inc(v_a_4657_);
if (v_isShared_4660_ == 0)
{
lean_ctor_set_tag(v___x_4659_, 1);
v___x_4662_ = v___x_4659_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_a_4657_);
v___x_4662_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
lean_object* v___x_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4670_; 
v___x_4663_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(v___y_4617_, v_isExporting_4624_, v___x_4640_, v___y_4615_, v___x_4652_, v___x_4662_);
lean_dec_ref(v___x_4662_);
v_isSharedCheck_4670_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4670_ == 0)
{
lean_object* v_unused_4671_; 
v_unused_4671_ = lean_ctor_get(v___x_4663_, 0);
lean_dec(v_unused_4671_);
v___x_4665_ = v___x_4663_;
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
else
{
lean_dec(v___x_4663_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___x_4668_; 
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 0, v_a_4657_);
v___x_4668_ = v___x_4665_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4657_);
v___x_4668_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
return v___x_4668_;
}
}
}
}
}
else
{
lean_object* v_a_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4683_; 
v_a_4674_ = lean_ctor_get(v_r_4656_, 0);
lean_inc(v_a_4674_);
lean_dec_ref_known(v_r_4656_, 1);
v___x_4675_ = lean_box(0);
v___x_4676_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(v___y_4617_, v_isExporting_4624_, v___x_4640_, v___y_4615_, v___x_4652_, v___x_4675_);
v_isSharedCheck_4683_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4683_ == 0)
{
lean_object* v_unused_4684_; 
v_unused_4684_ = lean_ctor_get(v___x_4676_, 0);
lean_dec(v_unused_4684_);
v___x_4678_ = v___x_4676_;
v_isShared_4679_ = v_isSharedCheck_4683_;
goto v_resetjp_4677_;
}
else
{
lean_dec(v___x_4676_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4683_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v___x_4681_; 
if (v_isShared_4679_ == 0)
{
lean_ctor_set_tag(v___x_4678_, 1);
lean_ctor_set(v___x_4678_, 0, v_a_4674_);
v___x_4681_ = v___x_4678_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v_a_4674_);
v___x_4681_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
return v___x_4681_;
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
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4610_ = stack[0].m_obj;
uint8_t v_isExporting_4611_ = stack[1].m_num;
lean_object* v___y_4612_ = stack[2].m_obj;
lean_object* v___y_4613_ = stack[3].m_obj;
lean_object* v___y_4614_ = stack[4].m_obj;
lean_object* v___y_4615_ = stack[5].m_obj;
lean_object* v___y_4616_ = stack[6].m_obj;
lean_object* v___y_4617_ = stack[7].m_obj;
lean_object* v_res_4693_;
v_res_4693_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(v_x_4610_, v_isExporting_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_);
stack->m_obj
 = v_res_4693_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___boxed(lean_object* v_x_4694_, lean_object* v_isExporting_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_){
_start:
{
uint8_t v_isExporting_boxed_4703_; lean_object* v_res_4704_; 
v_isExporting_boxed_4703_ = lean_unbox(v_isExporting_4695_);
v_res_4704_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(v_x_4694_, v_isExporting_boxed_4703_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_);
lean_dec(v___y_4701_);
lean_dec_ref(v___y_4700_);
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
return v_res_4704_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(lean_object* v_x_4705_, uint8_t v_when_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_){
_start:
{
if (v_when_4706_ == 0)
{
lean_object* v___x_4714_; 
lean_inc(v___y_4712_);
lean_inc_ref(v___y_4711_);
lean_inc(v___y_4710_);
lean_inc_ref(v___y_4709_);
lean_inc(v___y_4708_);
lean_inc_ref(v___y_4707_);
v___x_4714_ = lean_apply_7(v_x_4705_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, lean_box(0));
return v___x_4714_;
}
else
{
uint8_t v___x_4715_; lean_object* v___x_4716_; 
v___x_4715_ = 0;
v___x_4716_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(v_x_4705_, v___x_4715_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_);
return v___x_4716_;
}
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4705_ = stack[0].m_obj;
uint8_t v_when_4706_ = stack[1].m_num;
lean_object* v___y_4707_ = stack[2].m_obj;
lean_object* v___y_4708_ = stack[3].m_obj;
lean_object* v___y_4709_ = stack[4].m_obj;
lean_object* v___y_4710_ = stack[5].m_obj;
lean_object* v___y_4711_ = stack[6].m_obj;
lean_object* v___y_4712_ = stack[7].m_obj;
lean_object* v_res_4717_;
v_res_4717_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(v_x_4705_, v_when_4706_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_);
stack->m_obj
 = v_res_4717_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg___boxed(lean_object* v_x_4718_, lean_object* v_when_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_){
_start:
{
uint8_t v_when_boxed_4727_; lean_object* v_res_4728_; 
v_when_boxed_4727_ = lean_unbox(v_when_4719_);
v_res_4728_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(v_x_4718_, v_when_boxed_4727_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_);
lean_dec(v___y_4725_);
lean_dec_ref(v___y_4724_);
lean_dec(v___y_4723_);
lean_dec_ref(v___y_4722_);
lean_dec(v___y_4721_);
lean_dec_ref(v___y_4720_);
return v_res_4728_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___closed__2(void){
_start:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; 
v___x_4731_ = ((lean_object*)(l_Lean_Meta_Sym_letToHave___closed__1));
v___x_4732_ = l_Lean_stringToMessageData(v___x_4731_);
return v___x_4732_;
}
}
lean_object* l_Lean_Meta_Sym_letToHave(lean_object* v_e_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_){
_start:
{
lean_object* v___f_4741_; lean_object* v___f_4742_; lean_object* v___y_4744_; lean_object* v___y_4745_; lean_object* v___y_4746_; lean_object* v___y_4747_; lean_object* v___y_4748_; lean_object* v___y_4749_; uint8_t v___x_4758_; 
v___f_4741_ = ((lean_object*)(l_Lean_Meta_Sym_letToHave___closed__0));
lean_inc_ref(v_e_4733_);
v___f_4742_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_letToHave___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4742_, 0, v_e_4733_);
v___x_4758_ = l_Lean_Expr_hasLooseBVars(v_e_4733_);
lean_dec_ref(v_e_4733_);
if (v___x_4758_ == 0)
{
v___y_4744_ = v_a_4734_;
v___y_4745_ = v_a_4735_;
v___y_4746_ = v_a_4736_;
v___y_4747_ = v_a_4737_;
v___y_4748_ = v_a_4738_;
v___y_4749_ = v_a_4739_;
goto v___jp_4743_;
}
else
{
lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v_a_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4768_; 
lean_dec_ref(v___f_4742_);
v___x_4759_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___closed__2, &l_Lean_Meta_Sym_letToHave___closed__2_once, _init_l_Lean_Meta_Sym_letToHave___closed__2);
v___x_4760_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(v___x_4759_, v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_);
v_a_4761_ = lean_ctor_get(v___x_4760_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4760_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4763_ = v___x_4760_;
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_a_4761_);
lean_dec(v___x_4760_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4766_; 
if (v_isShared_4764_ == 0)
{
v___x_4766_ = v___x_4763_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_a_4761_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
}
v___jp_4743_:
{
uint8_t v___x_4750_; lean_object* v___x_4751_; lean_object* v___f_4752_; uint8_t v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; uint8_t v___x_4756_; lean_object* v___x_4757_; 
v___x_4750_ = 0;
v___x_4751_ = lean_box(v___x_4750_);
v___f_4752_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_letToHave___lam__5___boxed), 10, 3);
lean_closure_set(v___f_4752_, 0, v___x_4751_);
lean_closure_set(v___f_4752_, 1, v___f_4741_);
lean_closure_set(v___f_4752_, 2, v___f_4742_);
v___x_4753_ = 0;
v___x_4754_ = lean_box(v___x_4753_);
v___x_4755_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___boxed), 10, 3);
lean_closure_set(v___x_4755_, 0, lean_box(0));
lean_closure_set(v___x_4755_, 1, v___f_4752_);
lean_closure_set(v___x_4755_, 2, v___x_4754_);
v___x_4756_ = 1;
v___x_4757_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(v___x_4755_, v___x_4756_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_);
return v___x_4757_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_letToHave_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4733_ = stack[0].m_obj;
lean_object* v_a_4734_ = stack[1].m_obj;
lean_object* v_a_4735_ = stack[2].m_obj;
lean_object* v_a_4736_ = stack[3].m_obj;
lean_object* v_a_4737_ = stack[4].m_obj;
lean_object* v_a_4738_ = stack[5].m_obj;
lean_object* v_a_4739_ = stack[6].m_obj;
lean_object* v_res_4769_;
v_res_4769_ = l_Lean_Meta_Sym_letToHave(v_e_4733_, v_a_4734_, v_a_4735_, v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_);
stack->m_obj
 = v_res_4769_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___boxed(lean_object* v_e_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_){
_start:
{
lean_object* v_res_4778_; 
v_res_4778_ = l_Lean_Meta_Sym_letToHave(v_e_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_);
lean_dec(v_a_4776_);
lean_dec_ref(v_a_4775_);
lean_dec(v_a_4774_);
lean_dec_ref(v_a_4773_);
lean_dec(v_a_4772_);
lean_dec_ref(v_a_4771_);
return v_res_4778_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2(lean_object* v_00_u03b1_4779_, lean_object* v_x_4780_, uint8_t v_isExporting_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_){
_start:
{
lean_object* v___x_4789_; 
v___x_4789_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(v_x_4780_, v_isExporting_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_);
return v___x_4789_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4780_ = stack[1].m_obj;
uint8_t v_isExporting_4781_ = stack[2].m_num;
lean_object* v___y_4782_ = stack[3].m_obj;
lean_object* v___y_4783_ = stack[4].m_obj;
lean_object* v___y_4784_ = stack[5].m_obj;
lean_object* v___y_4785_ = stack[6].m_obj;
lean_object* v___y_4786_ = stack[7].m_obj;
lean_object* v___y_4787_ = stack[8].m_obj;
lean_object* v_res_4790_;
v_res_4790_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2(lean_box(0), v_x_4780_, v_isExporting_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_);
stack->m_obj
 = v_res_4790_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___boxed(lean_object* v_00_u03b1_4791_, lean_object* v_x_4792_, lean_object* v_isExporting_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_){
_start:
{
uint8_t v_isExporting_boxed_4801_; lean_object* v_res_4802_; 
v_isExporting_boxed_4801_ = lean_unbox(v_isExporting_4793_);
v_res_4802_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2(v_00_u03b1_4791_, v_x_4792_, v_isExporting_boxed_4801_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
lean_dec(v___y_4799_);
lean_dec_ref(v___y_4798_);
lean_dec(v___y_4797_);
lean_dec_ref(v___y_4796_);
lean_dec(v___y_4795_);
lean_dec_ref(v___y_4794_);
return v_res_4802_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2(lean_object* v_00_u03b1_4803_, lean_object* v_x_4804_, uint8_t v_when_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_){
_start:
{
lean_object* v___x_4813_; 
v___x_4813_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(v_x_4804_, v_when_4805_, v___y_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_);
return v___x_4813_;
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4804_ = stack[1].m_obj;
uint8_t v_when_4805_ = stack[2].m_num;
lean_object* v___y_4806_ = stack[3].m_obj;
lean_object* v___y_4807_ = stack[4].m_obj;
lean_object* v___y_4808_ = stack[5].m_obj;
lean_object* v___y_4809_ = stack[6].m_obj;
lean_object* v___y_4810_ = stack[7].m_obj;
lean_object* v___y_4811_ = stack[8].m_obj;
lean_object* v_res_4814_;
v_res_4814_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2(lean_box(0), v_x_4804_, v_when_4805_, v___y_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_);
stack->m_obj
 = v_res_4814_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___boxed(lean_object* v_00_u03b1_4815_, lean_object* v_x_4816_, lean_object* v_when_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_){
_start:
{
uint8_t v_when_boxed_4825_; lean_object* v_res_4826_; 
v_when_boxed_4825_ = lean_unbox(v_when_4817_);
v_res_4826_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2(v_00_u03b1_4815_, v_x_4816_, v_when_boxed_4825_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_, v___y_4823_);
lean_dec(v___y_4823_);
lean_dec_ref(v___y_4822_);
lean_dec(v___y_4821_);
lean_dec_ref(v___y_4820_);
lean_dec(v___y_4819_);
lean_dec_ref(v___y_4818_);
return v_res_4826_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3(lean_object* v_00_u03b1_4827_, lean_object* v_msg_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_){
_start:
{
lean_object* v___x_4836_; 
v___x_4836_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(v_msg_4828_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_);
return v___x_4836_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4828_ = stack[1].m_obj;
lean_object* v___y_4829_ = stack[2].m_obj;
lean_object* v___y_4830_ = stack[3].m_obj;
lean_object* v___y_4831_ = stack[4].m_obj;
lean_object* v___y_4832_ = stack[5].m_obj;
lean_object* v___y_4833_ = stack[6].m_obj;
lean_object* v___y_4834_ = stack[7].m_obj;
lean_object* v_res_4837_;
v_res_4837_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3(lean_box(0), v_msg_4828_, v___y_4829_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_);
stack->m_obj
 = v_res_4837_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___boxed(lean_object* v_00_u03b1_4838_, lean_object* v_msg_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_){
_start:
{
lean_object* v_res_4847_; 
v_res_4847_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3(v_00_u03b1_4838_, v_msg_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec(v___y_4841_);
lean_dec_ref(v___y_4840_);
return v_res_4847_;
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
