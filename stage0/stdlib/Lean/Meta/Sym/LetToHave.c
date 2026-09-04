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
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getZetaDeltaFVarIds___redArg(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__3;
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
lean_object* v___x_605_; lean_object* v___x_10876__overap_606_; lean_object* v___x_607_; 
v___x_605_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1___closed__0);
v___x_10876__overap_606_ = lean_panic_fn_borrowed(v___x_605_, v_msg_597_);
lean_inc(v___y_603_);
lean_inc_ref(v___y_602_);
lean_inc(v___y_601_);
lean_inc_ref(v___y_600_);
lean_inc(v___y_599_);
lean_inc_ref(v___y_598_);
v___x_607_ = lean_apply_7(v___x_10876__overap_606_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, lean_box(0));
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
uint8_t v___y_33873__boxed_675_; lean_object* v_res_676_; 
v___y_33873__boxed_675_ = lean_unbox(v___y_672_);
v_res_676_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1(v_f_669_, v_a_670_, v___y_671_, v___y_33873__boxed_675_, v___y_673_, v___y_674_);
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
lean_object* v_key_680_; lean_object* v_value_681_; lean_object* v_tail_682_; lean_object* v_fst_683_; lean_object* v_snd_684_; lean_object* v_fst_685_; lean_object* v_snd_686_; size_t v___x_687_; size_t v___x_688_; uint8_t v___x_689_; 
v_key_680_ = lean_ctor_get(v_x_678_, 0);
v_value_681_ = lean_ctor_get(v_x_678_, 1);
v_tail_682_ = lean_ctor_get(v_x_678_, 2);
v_fst_683_ = lean_ctor_get(v_key_680_, 0);
v_snd_684_ = lean_ctor_get(v_key_680_, 1);
v_fst_685_ = lean_ctor_get(v_a_677_, 0);
v_snd_686_ = lean_ctor_get(v_a_677_, 1);
v___x_687_ = lean_ptr_addr(v_fst_683_);
v___x_688_ = lean_ptr_addr(v_fst_685_);
v___x_689_ = lean_usize_dec_eq(v___x_687_, v___x_688_);
if (v___x_689_ == 0)
{
v_x_678_ = v_tail_682_;
goto _start;
}
else
{
uint8_t v___x_691_; 
v___x_691_ = lean_nat_dec_eq(v_snd_684_, v_snd_686_);
if (v___x_691_ == 0)
{
v_x_678_ = v_tail_682_;
goto _start;
}
else
{
lean_object* v___x_693_; 
lean_inc(v_value_681_);
v___x_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_693_, 0, v_value_681_);
return v___x_693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_a_694_, lean_object* v_x_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_694_, v_x_695_);
lean_dec(v_x_695_);
lean_dec_ref(v_a_694_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___redArg(lean_object* v_m_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_buckets_699_; lean_object* v_fst_700_; lean_object* v_snd_701_; lean_object* v___x_702_; size_t v___x_703_; size_t v___x_704_; size_t v___x_705_; uint64_t v___x_706_; uint64_t v___x_707_; uint64_t v___x_708_; uint64_t v___x_709_; uint64_t v___x_710_; uint64_t v_fold_711_; uint64_t v___x_712_; uint64_t v___x_713_; uint64_t v___x_714_; size_t v___x_715_; size_t v___x_716_; size_t v___x_717_; size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_buckets_699_ = lean_ctor_get(v_m_697_, 1);
v_fst_700_ = lean_ctor_get(v_a_698_, 0);
v_snd_701_ = lean_ctor_get(v_a_698_, 1);
v___x_702_ = lean_array_get_size(v_buckets_699_);
v___x_703_ = lean_ptr_addr(v_fst_700_);
v___x_704_ = ((size_t)3ULL);
v___x_705_ = lean_usize_shift_right(v___x_703_, v___x_704_);
v___x_706_ = lean_usize_to_uint64(v___x_705_);
v___x_707_ = lean_uint64_of_nat(v_snd_701_);
v___x_708_ = lean_uint64_mix_hash(v___x_706_, v___x_707_);
v___x_709_ = 32ULL;
v___x_710_ = lean_uint64_shift_right(v___x_708_, v___x_709_);
v_fold_711_ = lean_uint64_xor(v___x_708_, v___x_710_);
v___x_712_ = 16ULL;
v___x_713_ = lean_uint64_shift_right(v_fold_711_, v___x_712_);
v___x_714_ = lean_uint64_xor(v_fold_711_, v___x_713_);
v___x_715_ = lean_uint64_to_usize(v___x_714_);
v___x_716_ = lean_usize_of_nat(v___x_702_);
v___x_717_ = ((size_t)1ULL);
v___x_718_ = lean_usize_sub(v___x_716_, v___x_717_);
v___x_719_ = lean_usize_land(v___x_715_, v___x_718_);
v___x_720_ = lean_array_uget_borrowed(v_buckets_699_, v___x_719_);
v___x_721_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_698_, v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___redArg(v_m_722_, v_a_723_);
lean_dec_ref(v_a_723_);
lean_dec_ref(v_m_722_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7(lean_object* v_msg_732_, lean_object* v___y_733_, uint8_t v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___f_737_; lean_object* v___f_738_; lean_object* v___f_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___f_749_; lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___f_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_33404__overap_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___f_737_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__0));
v___f_738_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__1));
v___f_739_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__2));
v___x_740_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__3));
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v___f_737_);
v___x_742_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__4));
v___x_743_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__5));
v___x_744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_744_, 0, v___x_741_);
lean_ctor_set(v___x_744_, 1, v___x_742_);
lean_ctor_set(v___x_744_, 2, v___f_738_);
lean_ctor_set(v___x_744_, 3, v___f_739_);
lean_ctor_set(v___x_744_, 4, v___x_743_);
v___x_745_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___closed__6));
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = l_ReaderT_instMonad___redArg(v___x_746_);
v___x_748_ = l_ReaderT_instMonad___redArg(v___x_747_);
lean_inc_ref_n(v___x_748_, 6);
v___f_749_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_749_, 0, v___x_748_);
v___f_750_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_750_, 0, v___x_748_);
v___f_751_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_751_, 0, v___x_748_);
v___f_752_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_752_, 0, v___x_748_);
v___x_753_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_753_, 0, lean_box(0));
lean_closure_set(v___x_753_, 1, lean_box(0));
lean_closure_set(v___x_753_, 2, v___x_748_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v___f_749_);
v___x_755_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_755_, 0, lean_box(0));
lean_closure_set(v___x_755_, 1, lean_box(0));
lean_closure_set(v___x_755_, 2, v___x_748_);
v___x_756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_756_, 0, v___x_754_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
lean_ctor_set(v___x_756_, 2, v___f_750_);
lean_ctor_set(v___x_756_, 3, v___f_751_);
lean_ctor_set(v___x_756_, 4, v___f_752_);
v___x_757_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_757_, 0, lean_box(0));
lean_closure_set(v___x_757_, 1, lean_box(0));
lean_closure_set(v___x_757_, 2, v___x_748_);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = l_Lean_instInhabitedExpr;
v___x_760_ = l_instInhabitedOfMonad___redArg(v___x_758_, v___x_759_);
v___x_33404__overap_761_ = lean_panic_fn_borrowed(v___x_760_, v_msg_732_);
lean_dec(v___x_760_);
v___x_762_ = lean_box(v___y_734_);
lean_inc_ref(v___y_735_);
v___x_763_ = lean_apply_4(v___x_33404__overap_761_, v___y_733_, v___x_762_, v___y_735_, v___y_736_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7___boxed(lean_object* v_msg_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
uint8_t v___y_34070__boxed_769_; lean_object* v_res_770_; 
v___y_34070__boxed_769_ = lean_unbox(v___y_766_);
v_res_770_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7(v_msg_764_, v___y_765_, v___y_34070__boxed_769_, v___y_767_, v___y_768_);
lean_dec_ref(v___y_767_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__6(lean_object* v_structName_771_, lean_object* v_idx_772_, lean_object* v_struct_773_, lean_object* v___y_774_, uint8_t v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v___y_779_; lean_object* v___y_780_; 
if (v___y_775_ == 0)
{
v___y_779_ = v___y_774_;
v___y_780_ = v___y_777_;
goto v___jp_778_;
}
else
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_773_, v___y_775_, v___y_776_, v___y_777_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; 
v_a_803_ = lean_ctor_get(v___x_802_, 1);
lean_inc(v_a_803_);
lean_dec_ref_known(v___x_802_, 2);
v___y_779_ = v___y_774_;
v___y_780_ = v_a_803_;
goto v___jp_778_;
}
else
{
lean_object* v_a_804_; lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec_ref(v___y_774_);
lean_dec_ref(v_struct_773_);
lean_dec(v_idx_772_);
lean_dec(v_structName_771_);
v_a_804_ = lean_ctor_get(v___x_802_, 0);
v_a_805_ = lean_ctor_get(v___x_802_, 1);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_802_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_inc(v_a_804_);
lean_dec(v___x_802_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_804_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
v___jp_778_:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = l_Lean_Expr_proj___override(v_structName_771_, v_idx_772_, v_struct_773_);
v___x_782_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_781_, v___y_780_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_792_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
v_a_784_ = lean_ctor_get(v___x_782_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_792_ == 0)
{
v___x_786_ = v___x_782_;
v_isShared_787_ = v_isSharedCheck_792_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_inc(v_a_783_);
lean_dec(v___x_782_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_792_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v_a_783_);
lean_ctor_set(v___x_788_, 1, v___y_779_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_788_);
v___x_790_ = v___x_786_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_a_784_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
else
{
lean_object* v_a_793_; lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec_ref(v___y_779_);
v_a_793_ = lean_ctor_get(v___x_782_, 0);
v_a_794_ = lean_ctor_get(v___x_782_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_782_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_inc(v_a_793_);
lean_dec(v___x_782_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_793_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_a_794_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__6___boxed(lean_object* v_structName_813_, lean_object* v_idx_814_, lean_object* v_struct_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
uint8_t v___y_34141__boxed_820_; lean_object* v_res_821_; 
v___y_34141__boxed_820_ = lean_unbox(v___y_817_);
v_res_821_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__6(v_structName_813_, v_idx_814_, v_struct_815_, v___y_816_, v___y_34141__boxed_820_, v___y_818_, v___y_819_);
lean_dec_ref(v___y_818_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4(lean_object* v_x_822_, lean_object* v_t_823_, lean_object* v_v_824_, lean_object* v_b_825_, uint8_t v_nondep_826_, lean_object* v___y_827_, uint8_t v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v___y_832_; lean_object* v___y_833_; 
if (v___y_828_ == 0)
{
v___y_832_ = v___y_827_;
v___y_833_ = v___y_830_;
goto v___jp_831_;
}
else
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_823_, v___y_828_, v___y_829_, v___y_830_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_857_; 
v_a_856_ = lean_ctor_get(v___x_855_, 1);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_855_, 2);
v___x_857_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_824_, v___y_828_, v___y_829_, v_a_856_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; 
v_a_858_ = lean_ctor_get(v___x_857_, 1);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 2);
v___x_859_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_825_, v___y_828_, v___y_829_, v_a_858_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; 
v_a_860_ = lean_ctor_get(v___x_859_, 1);
lean_inc(v_a_860_);
lean_dec_ref_known(v___x_859_, 2);
v___y_832_ = v___y_827_;
v___y_833_ = v_a_860_;
goto v___jp_831_;
}
else
{
lean_object* v_a_861_; lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec_ref(v___y_827_);
lean_dec_ref(v_b_825_);
lean_dec_ref(v_v_824_);
lean_dec_ref(v_t_823_);
lean_dec(v_x_822_);
v_a_861_ = lean_ctor_get(v___x_859_, 0);
v_a_862_ = lean_ctor_get(v___x_859_, 1);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_859_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_inc(v_a_861_);
lean_dec(v___x_859_);
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
else
{
lean_object* v_a_870_; lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_dec_ref(v___y_827_);
lean_dec_ref(v_b_825_);
lean_dec_ref(v_v_824_);
lean_dec_ref(v_t_823_);
lean_dec(v_x_822_);
v_a_870_ = lean_ctor_get(v___x_857_, 0);
v_a_871_ = lean_ctor_get(v___x_857_, 1);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_857_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_inc(v_a_870_);
lean_dec(v___x_857_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_870_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
else
{
lean_object* v_a_879_; lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec_ref(v___y_827_);
lean_dec_ref(v_b_825_);
lean_dec_ref(v_v_824_);
lean_dec_ref(v_t_823_);
lean_dec(v_x_822_);
v_a_879_ = lean_ctor_get(v___x_855_, 0);
v_a_880_ = lean_ctor_get(v___x_855_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_855_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_inc(v_a_879_);
lean_dec(v___x_855_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_879_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
v___jp_831_:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = l_Lean_Expr_letE___override(v_x_822_, v_t_823_, v_v_824_, v_b_825_, v_nondep_826_);
v___x_835_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_834_, v___y_833_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_845_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
v_a_837_ = lean_ctor_get(v___x_835_, 1);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_845_ == 0)
{
v___x_839_ = v___x_835_;
v_isShared_840_ = v_isSharedCheck_845_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_inc(v_a_836_);
lean_dec(v___x_835_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_845_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_841_, 0, v_a_836_);
lean_ctor_set(v___x_841_, 1, v___y_832_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_841_);
v___x_843_ = v___x_839_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v_a_837_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
else
{
lean_object* v_a_846_; lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec_ref(v___y_832_);
v_a_846_ = lean_ctor_get(v___x_835_, 0);
v_a_847_ = lean_ctor_get(v___x_835_, 1);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_835_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_inc(v_a_846_);
lean_dec(v___x_835_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_846_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4___boxed(lean_object* v_x_888_, lean_object* v_t_889_, lean_object* v_v_890_, lean_object* v_b_891_, lean_object* v_nondep_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
uint8_t v_nondep_boxed_897_; uint8_t v___y_34224__boxed_898_; lean_object* v_res_899_; 
v_nondep_boxed_897_ = lean_unbox(v_nondep_892_);
v___y_34224__boxed_898_ = lean_unbox(v___y_894_);
v_res_899_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4(v_x_888_, v_t_889_, v_v_890_, v_b_891_, v_nondep_boxed_897_, v___y_893_, v___y_34224__boxed_898_, v___y_895_, v___y_896_);
lean_dec_ref(v___y_895_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2(lean_object* v_x_900_, uint8_t v_bi_901_, lean_object* v_t_902_, lean_object* v_b_903_, lean_object* v___y_904_, uint8_t v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___y_909_; lean_object* v___y_910_; 
if (v___y_905_ == 0)
{
v___y_909_ = v___y_904_;
v___y_910_ = v___y_907_;
goto v___jp_908_;
}
else
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_902_, v___y_905_, v___y_906_, v___y_907_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_934_; 
v_a_933_ = lean_ctor_get(v___x_932_, 1);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_932_, 2);
v___x_934_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_903_, v___y_905_, v___y_906_, v_a_933_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; 
v_a_935_ = lean_ctor_get(v___x_934_, 1);
lean_inc(v_a_935_);
lean_dec_ref_known(v___x_934_, 2);
v___y_909_ = v___y_904_;
v___y_910_ = v_a_935_;
goto v___jp_908_;
}
else
{
lean_object* v_a_936_; lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v___y_904_);
lean_dec_ref(v_b_903_);
lean_dec_ref(v_t_902_);
lean_dec(v_x_900_);
v_a_936_ = lean_ctor_get(v___x_934_, 0);
v_a_937_ = lean_ctor_get(v___x_934_, 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_934_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_inc(v_a_936_);
lean_dec(v___x_934_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_936_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
else
{
lean_object* v_a_945_; lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec_ref(v___y_904_);
lean_dec_ref(v_b_903_);
lean_dec_ref(v_t_902_);
lean_dec(v_x_900_);
v_a_945_ = lean_ctor_get(v___x_932_, 0);
v_a_946_ = lean_ctor_get(v___x_932_, 1);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_932_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_inc(v_a_945_);
lean_dec(v___x_932_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_945_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
v___jp_908_:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = l_Lean_Expr_lam___override(v_x_900_, v_t_902_, v_b_903_, v_bi_901_);
v___x_912_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_911_, v___y_910_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_922_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
v_a_914_ = lean_ctor_get(v___x_912_, 1);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_922_ == 0)
{
v___x_916_ = v___x_912_;
v_isShared_917_ = v_isSharedCheck_922_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_inc(v_a_913_);
lean_dec(v___x_912_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_922_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_918_, 0, v_a_913_);
lean_ctor_set(v___x_918_, 1, v___y_909_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_918_);
v___x_920_ = v___x_916_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_a_914_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
else
{
lean_object* v_a_923_; lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec_ref(v___y_909_);
v_a_923_ = lean_ctor_get(v___x_912_, 0);
v_a_924_ = lean_ctor_get(v___x_912_, 1);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_912_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_inc(v_a_923_);
lean_dec(v___x_912_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_923_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2___boxed(lean_object* v_x_954_, lean_object* v_bi_955_, lean_object* v_t_956_, lean_object* v_b_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
uint8_t v_bi_boxed_962_; uint8_t v___y_34353__boxed_963_; lean_object* v_res_964_; 
v_bi_boxed_962_ = lean_unbox(v_bi_955_);
v___y_34353__boxed_963_ = lean_unbox(v___y_959_);
v_res_964_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2(v_x_954_, v_bi_boxed_962_, v_t_956_, v_b_957_, v___y_958_, v___y_34353__boxed_963_, v___y_960_, v___y_961_);
lean_dec_ref(v___y_960_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__5(lean_object* v_d_965_, lean_object* v_e_966_, lean_object* v___y_967_, uint8_t v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___y_972_; lean_object* v___y_973_; 
if (v___y_968_ == 0)
{
v___y_972_ = v___y_967_;
v___y_973_ = v___y_970_;
goto v___jp_971_;
}
else
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_966_, v___y_968_, v___y_969_, v___y_970_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; 
v_a_996_ = lean_ctor_get(v___x_995_, 1);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_995_, 2);
v___y_972_ = v___y_967_;
v___y_973_ = v_a_996_;
goto v___jp_971_;
}
else
{
lean_object* v_a_997_; lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec_ref(v___y_967_);
lean_dec_ref(v_e_966_);
lean_dec(v_d_965_);
v_a_997_ = lean_ctor_get(v___x_995_, 0);
v_a_998_ = lean_ctor_get(v___x_995_, 1);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_995_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_inc(v_a_997_);
lean_dec(v___x_995_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_997_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
v___jp_971_:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = l_Lean_Expr_mdata___override(v_d_965_, v_e_966_);
v___x_975_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_974_, v___y_973_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_985_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_a_977_ = lean_ctor_get(v___x_975_, 1);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_985_ == 0)
{
v___x_979_ = v___x_975_;
v_isShared_980_ = v_isSharedCheck_985_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_985_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v_a_976_);
lean_ctor_set(v___x_981_, 1, v___y_972_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_981_);
v___x_983_ = v___x_979_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_a_977_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
else
{
lean_object* v_a_986_; lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec_ref(v___y_972_);
v_a_986_ = lean_ctor_get(v___x_975_, 0);
v_a_987_ = lean_ctor_get(v___x_975_, 1);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_975_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_inc(v_a_986_);
lean_dec(v___x_975_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_986_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__5___boxed(lean_object* v_d_1006_, lean_object* v_e_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
uint8_t v___y_34459__boxed_1012_; lean_object* v_res_1013_; 
v___y_34459__boxed_1012_ = lean_unbox(v___y_1009_);
v_res_1013_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__5(v_d_1006_, v_e_1007_, v___y_1008_, v___y_34459__boxed_1012_, v___y_1010_, v___y_1011_);
lean_dec_ref(v___y_1010_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3(lean_object* v_x_1014_, uint8_t v_bi_1015_, lean_object* v_t_1016_, lean_object* v_b_1017_, lean_object* v___y_1018_, uint8_t v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___y_1023_; lean_object* v___y_1024_; 
if (v___y_1019_ == 0)
{
v___y_1023_ = v___y_1018_;
v___y_1024_ = v___y_1021_;
goto v___jp_1022_;
}
else
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1016_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1048_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 1);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 2);
v___x_1048_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1017_, v___y_1019_, v___y_1020_, v_a_1047_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 1);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 2);
v___y_1023_ = v___y_1018_;
v___y_1024_ = v_a_1049_;
goto v___jp_1022_;
}
else
{
lean_object* v_a_1050_; lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec_ref(v___y_1018_);
lean_dec_ref(v_b_1017_);
lean_dec_ref(v_t_1016_);
lean_dec(v_x_1014_);
v_a_1050_ = lean_ctor_get(v___x_1048_, 0);
v_a_1051_ = lean_ctor_get(v___x_1048_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1048_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_inc(v_a_1050_);
lean_dec(v___x_1048_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1050_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
else
{
lean_object* v_a_1059_; lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec_ref(v___y_1018_);
lean_dec_ref(v_b_1017_);
lean_dec_ref(v_t_1016_);
lean_dec(v_x_1014_);
v_a_1059_ = lean_ctor_get(v___x_1046_, 0);
v_a_1060_ = lean_ctor_get(v___x_1046_, 1);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1046_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_inc(v_a_1059_);
lean_dec(v___x_1046_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1059_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_a_1060_);
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
v___jp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = l_Lean_Expr_forallE___override(v_x_1014_, v_t_1016_, v_b_1017_, v_bi_1015_);
v___x_1026_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1025_, v___y_1024_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1036_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_a_1028_ = lean_ctor_get(v___x_1026_, 1);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1030_ = v___x_1026_;
v_isShared_1031_ = v_isSharedCheck_1036_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1036_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v_a_1027_);
lean_ctor_set(v___x_1032_, 1, v___y_1023_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1032_);
v___x_1034_ = v___x_1030_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_a_1028_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec_ref(v___y_1023_);
v_a_1037_ = lean_ctor_get(v___x_1026_, 0);
v_a_1038_ = lean_ctor_get(v___x_1026_, 1);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1026_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_inc(v_a_1037_);
lean_dec(v___x_1026_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1037_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3___boxed(lean_object* v_x_1068_, lean_object* v_bi_1069_, lean_object* v_t_1070_, lean_object* v_b_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
uint8_t v_bi_boxed_1076_; uint8_t v___y_34542__boxed_1077_; lean_object* v_res_1078_; 
v_bi_boxed_1076_ = lean_unbox(v_bi_1069_);
v___y_34542__boxed_1077_ = lean_unbox(v___y_1073_);
v_res_1078_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3(v_x_1068_, v_bi_boxed_1076_, v_t_1070_, v_b_1071_, v___y_1072_, v___y_34542__boxed_1077_, v___y_1074_, v___y_1075_);
lean_dec_ref(v___y_1074_);
return v_res_1078_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1082_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_1083_ = lean_unsigned_to_nat(67u);
v___x_1084_ = lean_unsigned_to_nat(35u);
v___x_1085_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__1));
v___x_1086_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__0));
v___x_1087_ = l_mkPanicMessageWithDecl(v___x_1086_, v___x_1085_, v___x_1084_, v___x_1083_, v___x_1082_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0(lean_object* v___x_1088_, lean_object* v___x_1089_, lean_object* v_e_1090_, lean_object* v_offset_1091_, lean_object* v_a_1092_, uint8_t v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
switch(lean_obj_tag(v_e_1090_))
{
case 5:
{
lean_object* v_fn_1096_; lean_object* v_arg_1097_; lean_object* v___x_1098_; 
v_fn_1096_ = lean_ctor_get(v_e_1090_, 0);
v_arg_1097_ = lean_ctor_get(v_e_1090_, 1);
lean_inc(v_offset_1091_);
lean_inc_ref(v_fn_1096_);
v___x_1098_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1088_, v___x_1089_, v_fn_1096_, v_offset_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v_a_1100_; lean_object* v_fst_1101_; lean_object* v_snd_1102_; lean_object* v___x_1103_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
v_a_1100_ = lean_ctor_get(v___x_1098_, 1);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1098_, 2);
v_fst_1101_ = lean_ctor_get(v_a_1099_, 0);
lean_inc(v_fst_1101_);
v_snd_1102_ = lean_ctor_get(v_a_1099_, 1);
lean_inc(v_snd_1102_);
lean_dec(v_a_1099_);
lean_inc_ref(v_arg_1097_);
v___x_1103_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1088_, v___x_1089_, v_arg_1097_, v_offset_1091_, v_snd_1102_, v_a_1093_, v_a_1094_, v_a_1100_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1129_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_a_1105_ = lean_ctor_get(v___x_1103_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1107_ = v___x_1103_;
v_isShared_1108_ = v_isSharedCheck_1129_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1129_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v_fst_1109_; lean_object* v_snd_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1128_; 
v_fst_1109_ = lean_ctor_get(v_a_1104_, 0);
v_snd_1110_ = lean_ctor_get(v_a_1104_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_a_1104_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1112_ = v_a_1104_;
v_isShared_1113_ = v_isSharedCheck_1128_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_snd_1110_);
lean_inc(v_fst_1109_);
lean_dec(v_a_1104_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1128_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
size_t v___x_1114_; size_t v___x_1115_; uint8_t v___x_1116_; 
v___x_1114_ = lean_ptr_addr(v_fn_1096_);
v___x_1115_ = lean_ptr_addr(v_fst_1101_);
v___x_1116_ = lean_usize_dec_eq(v___x_1114_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
lean_del_object(v___x_1112_);
lean_del_object(v___x_1107_);
lean_dec_ref_known(v_e_1090_, 2);
v___x_1117_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1(v_fst_1101_, v_fst_1109_, v_snd_1110_, v_a_1093_, v_a_1094_, v_a_1105_);
return v___x_1117_;
}
else
{
size_t v___x_1118_; size_t v___x_1119_; uint8_t v___x_1120_; 
v___x_1118_ = lean_ptr_addr(v_arg_1097_);
v___x_1119_ = lean_ptr_addr(v_fst_1109_);
v___x_1120_ = lean_usize_dec_eq(v___x_1118_, v___x_1119_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; 
lean_del_object(v___x_1112_);
lean_del_object(v___x_1107_);
lean_dec_ref_known(v_e_1090_, 2);
v___x_1121_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__1(v_fst_1101_, v_fst_1109_, v_snd_1110_, v_a_1093_, v_a_1094_, v_a_1105_);
return v___x_1121_;
}
else
{
lean_object* v___x_1123_; 
lean_dec(v_fst_1109_);
lean_dec(v_fst_1101_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v_e_1090_);
v___x_1123_ = v___x_1112_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_e_1090_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_snd_1110_);
v___x_1123_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1125_; 
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v___x_1123_);
v___x_1125_ = v___x_1107_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_a_1105_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1101_);
lean_dec_ref_known(v_e_1090_, 2);
return v___x_1103_;
}
}
else
{
lean_dec_ref_known(v_e_1090_, 2);
lean_dec(v_offset_1091_);
return v___x_1098_;
}
}
case 6:
{
lean_object* v_binderName_1130_; lean_object* v_binderType_1131_; lean_object* v_body_1132_; uint8_t v_binderInfo_1133_; lean_object* v___x_1134_; 
v_binderName_1130_ = lean_ctor_get(v_e_1090_, 0);
v_binderType_1131_ = lean_ctor_get(v_e_1090_, 1);
v_body_1132_ = lean_ctor_get(v_e_1090_, 2);
v_binderInfo_1133_ = lean_ctor_get_uint8(v_e_1090_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1091_);
lean_inc_ref(v_binderType_1131_);
v___x_1134_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1088_, v___x_1089_, v_binderType_1131_, v_offset_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v_a_1136_; lean_object* v_fst_1137_; lean_object* v_snd_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1135_);
v_a_1136_ = lean_ctor_get(v___x_1134_, 1);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1134_, 2);
v_fst_1137_ = lean_ctor_get(v_a_1135_, 0);
lean_inc(v_fst_1137_);
v_snd_1138_ = lean_ctor_get(v_a_1135_, 1);
lean_inc(v_snd_1138_);
lean_dec(v_a_1135_);
v___x_1139_ = lean_unsigned_to_nat(1u);
v___x_1140_ = lean_nat_add(v_offset_1091_, v___x_1139_);
lean_dec(v_offset_1091_);
lean_inc_ref(v_body_1132_);
v___x_1141_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1088_, v___x_1089_, v_body_1132_, v___x_1140_, v_snd_1138_, v_a_1093_, v_a_1094_, v_a_1136_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1167_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
v_a_1143_ = lean_ctor_get(v___x_1141_, 1);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1145_ = v___x_1141_;
v_isShared_1146_ = v_isSharedCheck_1167_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_inc(v_a_1142_);
lean_dec(v___x_1141_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1167_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v_fst_1147_; lean_object* v_snd_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1166_; 
v_fst_1147_ = lean_ctor_get(v_a_1142_, 0);
v_snd_1148_ = lean_ctor_get(v_a_1142_, 1);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_a_1142_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1150_ = v_a_1142_;
v_isShared_1151_ = v_isSharedCheck_1166_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_snd_1148_);
lean_inc(v_fst_1147_);
lean_dec(v_a_1142_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1166_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
size_t v___x_1152_; size_t v___x_1153_; uint8_t v___x_1154_; 
v___x_1152_ = lean_ptr_addr(v_binderType_1131_);
v___x_1153_ = lean_ptr_addr(v_fst_1137_);
v___x_1154_ = lean_usize_dec_eq(v___x_1152_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; 
lean_inc(v_binderName_1130_);
lean_del_object(v___x_1150_);
lean_del_object(v___x_1145_);
lean_dec_ref_known(v_e_1090_, 3);
v___x_1155_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2(v_binderName_1130_, v_binderInfo_1133_, v_fst_1137_, v_fst_1147_, v_snd_1148_, v_a_1093_, v_a_1094_, v_a_1143_);
return v___x_1155_;
}
else
{
size_t v___x_1156_; size_t v___x_1157_; uint8_t v___x_1158_; 
v___x_1156_ = lean_ptr_addr(v_body_1132_);
v___x_1157_ = lean_ptr_addr(v_fst_1147_);
v___x_1158_ = lean_usize_dec_eq(v___x_1156_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; 
lean_inc(v_binderName_1130_);
lean_del_object(v___x_1150_);
lean_del_object(v___x_1145_);
lean_dec_ref_known(v_e_1090_, 3);
v___x_1159_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__2(v_binderName_1130_, v_binderInfo_1133_, v_fst_1137_, v_fst_1147_, v_snd_1148_, v_a_1093_, v_a_1094_, v_a_1143_);
return v___x_1159_;
}
else
{
lean_object* v___x_1161_; 
lean_dec(v_fst_1147_);
lean_dec(v_fst_1137_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v_e_1090_);
v___x_1161_ = v___x_1150_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_e_1090_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_snd_1148_);
v___x_1161_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1163_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1161_);
v___x_1163_ = v___x_1145_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_a_1143_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1137_);
lean_dec_ref_known(v_e_1090_, 3);
return v___x_1141_;
}
}
else
{
lean_dec_ref_known(v_e_1090_, 3);
lean_dec(v_offset_1091_);
return v___x_1134_;
}
}
case 7:
{
lean_object* v_binderName_1168_; lean_object* v_binderType_1169_; lean_object* v_body_1170_; uint8_t v_binderInfo_1171_; lean_object* v___x_1172_; 
v_binderName_1168_ = lean_ctor_get(v_e_1090_, 0);
v_binderType_1169_ = lean_ctor_get(v_e_1090_, 1);
v_body_1170_ = lean_ctor_get(v_e_1090_, 2);
v_binderInfo_1171_ = lean_ctor_get_uint8(v_e_1090_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1091_);
lean_inc_ref(v_binderType_1169_);
v___x_1172_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1088_, v___x_1089_, v_binderType_1169_, v_offset_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v_a_1174_; lean_object* v_fst_1175_; lean_object* v_snd_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
v_a_1174_ = lean_ctor_get(v___x_1172_, 1);
lean_inc(v_a_1174_);
lean_dec_ref_known(v___x_1172_, 2);
v_fst_1175_ = lean_ctor_get(v_a_1173_, 0);
lean_inc(v_fst_1175_);
v_snd_1176_ = lean_ctor_get(v_a_1173_, 1);
lean_inc(v_snd_1176_);
lean_dec(v_a_1173_);
v___x_1177_ = lean_unsigned_to_nat(1u);
v___x_1178_ = lean_nat_add(v_offset_1091_, v___x_1177_);
lean_dec(v_offset_1091_);
lean_inc_ref(v_body_1170_);
v___x_1179_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1088_, v___x_1089_, v_body_1170_, v___x_1178_, v_snd_1176_, v_a_1093_, v_a_1094_, v_a_1174_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1205_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
v_a_1181_ = lean_ctor_get(v___x_1179_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1183_ = v___x_1179_;
v_isShared_1184_ = v_isSharedCheck_1205_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_inc(v_a_1180_);
lean_dec(v___x_1179_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1205_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v_fst_1185_; lean_object* v_snd_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1204_; 
v_fst_1185_ = lean_ctor_get(v_a_1180_, 0);
v_snd_1186_ = lean_ctor_get(v_a_1180_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_a_1180_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1188_ = v_a_1180_;
v_isShared_1189_ = v_isSharedCheck_1204_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_snd_1186_);
lean_inc(v_fst_1185_);
lean_dec(v_a_1180_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1204_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
size_t v___x_1190_; size_t v___x_1191_; uint8_t v___x_1192_; 
v___x_1190_ = lean_ptr_addr(v_binderType_1169_);
v___x_1191_ = lean_ptr_addr(v_fst_1175_);
v___x_1192_ = lean_usize_dec_eq(v___x_1190_, v___x_1191_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; 
lean_inc(v_binderName_1168_);
lean_del_object(v___x_1188_);
lean_del_object(v___x_1183_);
lean_dec_ref_known(v_e_1090_, 3);
v___x_1193_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3(v_binderName_1168_, v_binderInfo_1171_, v_fst_1175_, v_fst_1185_, v_snd_1186_, v_a_1093_, v_a_1094_, v_a_1181_);
return v___x_1193_;
}
else
{
size_t v___x_1194_; size_t v___x_1195_; uint8_t v___x_1196_; 
v___x_1194_ = lean_ptr_addr(v_body_1170_);
v___x_1195_ = lean_ptr_addr(v_fst_1185_);
v___x_1196_ = lean_usize_dec_eq(v___x_1194_, v___x_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; 
lean_inc(v_binderName_1168_);
lean_del_object(v___x_1188_);
lean_del_object(v___x_1183_);
lean_dec_ref_known(v_e_1090_, 3);
v___x_1197_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__3(v_binderName_1168_, v_binderInfo_1171_, v_fst_1175_, v_fst_1185_, v_snd_1186_, v_a_1093_, v_a_1094_, v_a_1181_);
return v___x_1197_;
}
else
{
lean_object* v___x_1199_; 
lean_dec(v_fst_1185_);
lean_dec(v_fst_1175_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v_e_1090_);
v___x_1199_ = v___x_1188_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_e_1090_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_snd_1186_);
v___x_1199_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1201_; 
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v___x_1199_);
v___x_1201_ = v___x_1183_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_a_1181_);
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
}
}
else
{
lean_dec(v_fst_1175_);
lean_dec_ref_known(v_e_1090_, 3);
return v___x_1179_;
}
}
else
{
lean_dec_ref_known(v_e_1090_, 3);
lean_dec(v_offset_1091_);
return v___x_1172_;
}
}
case 8:
{
lean_object* v_declName_1206_; lean_object* v_type_1207_; lean_object* v_value_1208_; lean_object* v_body_1209_; uint8_t v_nondep_1210_; lean_object* v___x_1211_; 
v_declName_1206_ = lean_ctor_get(v_e_1090_, 0);
v_type_1207_ = lean_ctor_get(v_e_1090_, 1);
v_value_1208_ = lean_ctor_get(v_e_1090_, 2);
v_body_1209_ = lean_ctor_get(v_e_1090_, 3);
v_nondep_1210_ = lean_ctor_get_uint8(v_e_1090_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1091_);
lean_inc_ref(v_type_1207_);
v___x_1211_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1088_, v___x_1089_, v_type_1207_, v_offset_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v_a_1213_; lean_object* v_fst_1214_; lean_object* v_snd_1215_; lean_object* v___x_1216_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1212_);
v_a_1213_ = lean_ctor_get(v___x_1211_, 1);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1211_, 2);
v_fst_1214_ = lean_ctor_get(v_a_1212_, 0);
lean_inc(v_fst_1214_);
v_snd_1215_ = lean_ctor_get(v_a_1212_, 1);
lean_inc(v_snd_1215_);
lean_dec(v_a_1212_);
lean_inc(v_offset_1091_);
lean_inc_ref(v_value_1208_);
v___x_1216_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1088_, v___x_1089_, v_value_1208_, v_offset_1091_, v_snd_1215_, v_a_1093_, v_a_1094_, v_a_1213_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v_a_1218_; lean_object* v_fst_1219_; lean_object* v_snd_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
v_a_1218_ = lean_ctor_get(v___x_1216_, 1);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1216_, 2);
v_fst_1219_ = lean_ctor_get(v_a_1217_, 0);
lean_inc(v_fst_1219_);
v_snd_1220_ = lean_ctor_get(v_a_1217_, 1);
lean_inc(v_snd_1220_);
lean_dec(v_a_1217_);
v___x_1221_ = lean_unsigned_to_nat(1u);
v___x_1222_ = lean_nat_add(v_offset_1091_, v___x_1221_);
lean_dec(v_offset_1091_);
lean_inc_ref(v_body_1209_);
v___x_1223_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1088_, v___x_1089_, v_body_1209_, v___x_1222_, v_snd_1220_, v_a_1093_, v_a_1094_, v_a_1218_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1253_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
v_a_1225_ = lean_ctor_get(v___x_1223_, 1);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1227_ = v___x_1223_;
v_isShared_1228_ = v_isSharedCheck_1253_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_inc(v_a_1224_);
lean_dec(v___x_1223_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1253_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v_fst_1229_; lean_object* v_snd_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1252_; 
v_fst_1229_ = lean_ctor_get(v_a_1224_, 0);
v_snd_1230_ = lean_ctor_get(v_a_1224_, 1);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_a_1224_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1232_ = v_a_1224_;
v_isShared_1233_ = v_isSharedCheck_1252_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_snd_1230_);
lean_inc(v_fst_1229_);
lean_dec(v_a_1224_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1252_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
size_t v___x_1234_; size_t v___x_1235_; uint8_t v___x_1236_; 
v___x_1234_ = lean_ptr_addr(v_type_1207_);
v___x_1235_ = lean_ptr_addr(v_fst_1214_);
v___x_1236_ = lean_usize_dec_eq(v___x_1234_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; 
lean_inc(v_declName_1206_);
lean_del_object(v___x_1232_);
lean_del_object(v___x_1227_);
lean_dec_ref_known(v_e_1090_, 4);
v___x_1237_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4(v_declName_1206_, v_fst_1214_, v_fst_1219_, v_fst_1229_, v_nondep_1210_, v_snd_1230_, v_a_1093_, v_a_1094_, v_a_1225_);
return v___x_1237_;
}
else
{
size_t v___x_1238_; size_t v___x_1239_; uint8_t v___x_1240_; 
v___x_1238_ = lean_ptr_addr(v_value_1208_);
v___x_1239_ = lean_ptr_addr(v_fst_1219_);
v___x_1240_ = lean_usize_dec_eq(v___x_1238_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; 
lean_inc(v_declName_1206_);
lean_del_object(v___x_1232_);
lean_del_object(v___x_1227_);
lean_dec_ref_known(v_e_1090_, 4);
v___x_1241_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4(v_declName_1206_, v_fst_1214_, v_fst_1219_, v_fst_1229_, v_nondep_1210_, v_snd_1230_, v_a_1093_, v_a_1094_, v_a_1225_);
return v___x_1241_;
}
else
{
size_t v___x_1242_; size_t v___x_1243_; uint8_t v___x_1244_; 
v___x_1242_ = lean_ptr_addr(v_body_1209_);
v___x_1243_ = lean_ptr_addr(v_fst_1229_);
v___x_1244_ = lean_usize_dec_eq(v___x_1242_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; 
lean_inc(v_declName_1206_);
lean_del_object(v___x_1232_);
lean_del_object(v___x_1227_);
lean_dec_ref_known(v_e_1090_, 4);
v___x_1245_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__4(v_declName_1206_, v_fst_1214_, v_fst_1219_, v_fst_1229_, v_nondep_1210_, v_snd_1230_, v_a_1093_, v_a_1094_, v_a_1225_);
return v___x_1245_;
}
else
{
lean_object* v___x_1247_; 
lean_dec(v_fst_1229_);
lean_dec(v_fst_1219_);
lean_dec(v_fst_1214_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v_e_1090_);
v___x_1247_ = v___x_1232_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_e_1090_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_snd_1230_);
v___x_1247_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1249_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1247_);
v___x_1249_ = v___x_1227_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_a_1225_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
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
lean_dec(v_fst_1219_);
lean_dec(v_fst_1214_);
lean_dec_ref_known(v_e_1090_, 4);
return v___x_1223_;
}
}
else
{
lean_dec(v_fst_1214_);
lean_dec_ref_known(v_e_1090_, 4);
lean_dec(v_offset_1091_);
return v___x_1216_;
}
}
else
{
lean_dec_ref_known(v_e_1090_, 4);
lean_dec(v_offset_1091_);
return v___x_1211_;
}
}
case 10:
{
lean_object* v_data_1254_; lean_object* v_expr_1255_; lean_object* v___x_1256_; 
v_data_1254_ = lean_ctor_get(v_e_1090_, 0);
v_expr_1255_ = lean_ctor_get(v_e_1090_, 1);
lean_inc_ref(v_expr_1255_);
v___x_1256_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1088_, v___x_1089_, v_expr_1255_, v_offset_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1278_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_a_1258_ = lean_ctor_get(v___x_1256_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1260_ = v___x_1256_;
v_isShared_1261_ = v_isSharedCheck_1278_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1278_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v_fst_1262_; lean_object* v_snd_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1277_; 
v_fst_1262_ = lean_ctor_get(v_a_1257_, 0);
v_snd_1263_ = lean_ctor_get(v_a_1257_, 1);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_a_1257_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1265_ = v_a_1257_;
v_isShared_1266_ = v_isSharedCheck_1277_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_snd_1263_);
lean_inc(v_fst_1262_);
lean_dec(v_a_1257_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1277_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
size_t v___x_1267_; size_t v___x_1268_; uint8_t v___x_1269_; 
v___x_1267_ = lean_ptr_addr(v_expr_1255_);
v___x_1268_ = lean_ptr_addr(v_fst_1262_);
v___x_1269_ = lean_usize_dec_eq(v___x_1267_, v___x_1268_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; 
lean_inc(v_data_1254_);
lean_del_object(v___x_1265_);
lean_del_object(v___x_1260_);
lean_dec_ref_known(v_e_1090_, 2);
v___x_1270_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__5(v_data_1254_, v_fst_1262_, v_snd_1263_, v_a_1093_, v_a_1094_, v_a_1258_);
return v___x_1270_;
}
else
{
lean_object* v___x_1272_; 
lean_dec(v_fst_1262_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v_e_1090_);
v___x_1272_ = v___x_1265_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_e_1090_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_snd_1263_);
v___x_1272_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
lean_object* v___x_1274_; 
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v___x_1272_);
v___x_1274_ = v___x_1260_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_a_1258_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1090_, 2);
return v___x_1256_;
}
}
case 11:
{
lean_object* v_typeName_1279_; lean_object* v_idx_1280_; lean_object* v_struct_1281_; lean_object* v___x_1282_; 
v_typeName_1279_ = lean_ctor_get(v_e_1090_, 0);
v_idx_1280_ = lean_ctor_get(v_e_1090_, 1);
v_struct_1281_ = lean_ctor_get(v_e_1090_, 2);
lean_inc_ref(v_struct_1281_);
v___x_1282_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1088_, v___x_1089_, v_struct_1281_, v_offset_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1304_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_a_1284_ = lean_ctor_get(v___x_1282_, 1);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1286_ = v___x_1282_;
v_isShared_1287_ = v_isSharedCheck_1304_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1304_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v_fst_1288_; lean_object* v_snd_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1303_; 
v_fst_1288_ = lean_ctor_get(v_a_1283_, 0);
v_snd_1289_ = lean_ctor_get(v_a_1283_, 1);
v_isSharedCheck_1303_ = !lean_is_exclusive(v_a_1283_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1291_ = v_a_1283_;
v_isShared_1292_ = v_isSharedCheck_1303_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_snd_1289_);
lean_inc(v_fst_1288_);
lean_dec(v_a_1283_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1303_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
size_t v___x_1293_; size_t v___x_1294_; uint8_t v___x_1295_; 
v___x_1293_ = lean_ptr_addr(v_struct_1281_);
v___x_1294_ = lean_ptr_addr(v_fst_1288_);
v___x_1295_ = lean_usize_dec_eq(v___x_1293_, v___x_1294_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; 
lean_inc(v_idx_1280_);
lean_inc(v_typeName_1279_);
lean_del_object(v___x_1291_);
lean_del_object(v___x_1286_);
lean_dec_ref_known(v_e_1090_, 3);
v___x_1296_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__6(v_typeName_1279_, v_idx_1280_, v_fst_1288_, v_snd_1289_, v_a_1093_, v_a_1094_, v_a_1284_);
return v___x_1296_;
}
else
{
lean_object* v___x_1298_; 
lean_dec(v_fst_1288_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v_e_1090_);
v___x_1298_ = v___x_1291_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_e_1090_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_snd_1289_);
v___x_1298_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
lean_object* v___x_1300_; 
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1298_);
v___x_1300_ = v___x_1286_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_a_1284_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1090_, 3);
return v___x_1282_;
}
}
default: 
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
lean_dec(v_offset_1091_);
lean_dec_ref(v_e_1090_);
v___x_1305_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__3);
v___x_1306_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__7(v___x_1305_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
return v___x_1306_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(lean_object* v___x_1307_, lean_object* v___x_1308_, lean_object* v_e_1309_, lean_object* v_offset_1310_, lean_object* v_a_1311_, uint8_t v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v_key_1315_; lean_object* v___x_1316_; 
lean_inc(v_offset_1310_);
lean_inc_ref(v_e_1309_);
v_key_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1315_, 0, v_e_1309_);
lean_ctor_set(v_key_1315_, 1, v_offset_1310_);
v___x_1316_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___redArg(v_a_1311_, v_key_1315_);
if (lean_obj_tag(v___x_1316_) == 1)
{
lean_object* v_val_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_dec_ref_known(v_key_1315_, 2);
lean_dec(v_offset_1310_);
lean_dec_ref(v_e_1309_);
v_val_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_val_1317_);
lean_dec_ref_known(v___x_1316_, 1);
v___x_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1318_, 0, v_val_1317_);
lean_ctor_set(v___x_1318_, 1, v_a_1311_);
v___x_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
lean_ctor_set(v___x_1319_, 1, v_a_1314_);
return v___x_1319_;
}
else
{
lean_dec(v___x_1316_);
switch(lean_obj_tag(v_e_1309_))
{
case 0:
{
lean_object* v_deBruijnIndex_1320_; uint8_t v___x_1321_; 
v_deBruijnIndex_1320_ = lean_ctor_get(v_e_1309_, 0);
v___x_1321_ = lean_nat_dec_le(v_offset_1310_, v_deBruijnIndex_1320_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; 
lean_dec(v_offset_1310_);
v___x_1322_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1315_, v_e_1309_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1322_;
}
else
{
lean_object* v_size_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
lean_inc(v_deBruijnIndex_1320_);
lean_dec_ref_known(v_e_1309_, 1);
v_size_1323_ = lean_ctor_get(v___x_1308_, 2);
v___x_1324_ = l_Lean_instInhabitedExpr;
v___x_1325_ = lean_nat_sub(v_deBruijnIndex_1320_, v_offset_1310_);
lean_dec(v_offset_1310_);
lean_dec(v_deBruijnIndex_1320_);
v___x_1326_ = lean_nat_sub(v___x_1307_, v___x_1325_);
lean_dec(v___x_1325_);
v___x_1327_ = lean_unsigned_to_nat(1u);
v___x_1328_ = lean_nat_sub(v___x_1326_, v___x_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_nat_dec_lt(v___x_1328_, v_size_1323_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec(v___x_1328_);
v___x_1330_ = l_outOfBounds___redArg(v___x_1324_);
v___x_1331_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1315_, v___x_1330_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1331_;
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1324_, v___x_1308_, v___x_1328_);
lean_dec(v___x_1328_);
v___x_1333_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1315_, v___x_1332_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1333_;
}
}
}
case 9:
{
lean_object* v___x_1334_; 
lean_dec(v_offset_1310_);
v___x_1334_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1315_, v_e_1309_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1334_;
}
case 2:
{
lean_object* v___x_1335_; 
lean_dec(v_offset_1310_);
v___x_1335_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1315_, v_e_1309_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1335_;
}
case 1:
{
lean_object* v___x_1336_; 
lean_dec(v_offset_1310_);
v___x_1336_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1315_, v_e_1309_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1336_;
}
case 4:
{
lean_object* v___x_1337_; 
lean_dec(v_offset_1310_);
v___x_1337_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1315_, v_e_1309_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1337_;
}
case 3:
{
lean_object* v___x_1338_; 
lean_dec(v_offset_1310_);
v___x_1338_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1315_, v_e_1309_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1338_;
}
default: 
{
lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1339_ = l_Lean_Expr_looseBVarRange(v_e_1309_);
v___x_1340_ = lean_nat_dec_le(v___x_1339_, v_offset_1310_);
lean_dec(v___x_1339_);
if (v___x_1340_ == 0)
{
switch(lean_obj_tag(v_e_1309_))
{
case 9:
{
lean_object* v___x_1341_; 
lean_dec(v_offset_1310_);
v___x_1341_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1315_, v_e_1309_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1341_;
}
case 2:
{
lean_object* v___x_1342_; 
lean_dec(v_offset_1310_);
v___x_1342_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1315_, v_e_1309_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1342_;
}
case 0:
{
lean_object* v___x_1343_; 
lean_dec(v_offset_1310_);
v___x_1343_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1315_, v_e_1309_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1343_;
}
case 1:
{
lean_object* v___x_1344_; 
lean_dec(v_offset_1310_);
v___x_1344_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1315_, v_e_1309_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1344_;
}
case 4:
{
lean_object* v___x_1345_; 
lean_dec(v_offset_1310_);
v___x_1345_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1315_, v_e_1309_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1345_;
}
case 3:
{
lean_object* v___x_1346_; 
lean_dec(v_offset_1310_);
v___x_1346_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1315_, v_e_1309_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1346_;
}
default: 
{
lean_object* v___x_1347_; 
v___x_1347_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0(v___x_1307_, v___x_1308_, v_e_1309_, v_offset_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v_a_1349_; lean_object* v_fst_1350_; lean_object* v_snd_1351_; lean_object* v___x_1352_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
v_a_1349_ = lean_ctor_get(v___x_1347_, 1);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1347_, 2);
v_fst_1350_ = lean_ctor_get(v_a_1348_, 0);
lean_inc(v_fst_1350_);
v_snd_1351_ = lean_ctor_get(v_a_1348_, 1);
lean_inc(v_snd_1351_);
lean_dec(v_a_1348_);
v___x_1352_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1315_, v_fst_1350_, v_snd_1351_, v_a_1312_, v_a_1313_, v_a_1349_);
return v___x_1352_;
}
else
{
lean_dec_ref_known(v_key_1315_, 2);
return v___x_1347_;
}
}
}
}
else
{
lean_object* v___x_1353_; 
lean_dec(v_offset_1310_);
v___x_1353_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1315_, v_e_1309_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1353_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0___boxed(lean_object* v___x_1354_, lean_object* v___x_1355_, lean_object* v_e_1356_, lean_object* v_offset_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
uint8_t v_a_boxed_1362_; lean_object* v_res_1363_; 
v_a_boxed_1362_ = lean_unbox(v_a_1359_);
v_res_1363_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0(v___x_1354_, v___x_1355_, v_e_1356_, v_offset_1357_, v_a_1358_, v_a_boxed_1362_, v_a_1360_, v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec_ref(v___x_1355_);
lean_dec(v___x_1354_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___boxed(lean_object* v___x_1364_, lean_object* v___x_1365_, lean_object* v_e_1366_, lean_object* v_offset_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
uint8_t v_a_boxed_1372_; lean_object* v_res_1373_; 
v_a_boxed_1372_ = lean_unbox(v_a_1369_);
v_res_1373_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0(v___x_1364_, v___x_1365_, v_e_1366_, v_offset_1367_, v_a_1368_, v_a_boxed_1372_, v_a_1370_, v_a_1371_);
lean_dec_ref(v_a_1370_);
lean_dec_ref(v___x_1365_);
lean_dec(v___x_1364_);
return v_res_1373_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1374_ = lean_box(0);
v___x_1375_ = lean_unsigned_to_nat(16u);
v___x_1376_ = lean_mk_array(v___x_1375_, v___x_1374_);
return v___x_1376_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1377_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__0, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__0_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__0);
v___x_1378_ = lean_unsigned_to_nat(0u);
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
lean_ctor_set(v___x_1379_, 1, v___x_1377_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0(lean_object* v_e_1380_, lean_object* v_size_1381_, lean_object* v___x_1382_, lean_object* v_xs_1383_, uint8_t v_debug_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1380_))
{
case 0:
{
lean_object* v_deBruijnIndex_1388_; uint8_t v___x_1389_; 
v_deBruijnIndex_1388_ = lean_ctor_get(v_e_1380_, 0);
v___x_1389_ = lean_nat_dec_le(v___x_1387_, v_deBruijnIndex_1388_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v_e_1380_);
lean_ctor_set(v___x_1390_, 1, v___y_1386_);
return v___x_1390_;
}
else
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
lean_inc(v_deBruijnIndex_1388_);
lean_dec_ref_known(v_e_1380_, 1);
v___x_1391_ = lean_nat_sub(v_size_1381_, v_deBruijnIndex_1388_);
lean_dec(v_deBruijnIndex_1388_);
v___x_1392_ = lean_unsigned_to_nat(1u);
v___x_1393_ = lean_nat_sub(v___x_1391_, v___x_1392_);
lean_dec(v___x_1391_);
v___x_1394_ = lean_nat_dec_lt(v___x_1393_, v_size_1381_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_dec(v___x_1393_);
v___x_1395_ = l_outOfBounds___redArg(v___x_1382_);
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
lean_ctor_set(v___x_1396_, 1, v___y_1386_);
return v___x_1396_;
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1382_, v_xs_1383_, v___x_1393_);
lean_dec(v___x_1393_);
v___x_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
lean_ctor_set(v___x_1398_, 1, v___y_1386_);
return v___x_1398_;
}
}
}
case 9:
{
lean_object* v___x_1399_; 
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v_e_1380_);
lean_ctor_set(v___x_1399_, 1, v___y_1386_);
return v___x_1399_;
}
case 2:
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1400_, 0, v_e_1380_);
lean_ctor_set(v___x_1400_, 1, v___y_1386_);
return v___x_1400_;
}
case 1:
{
lean_object* v___x_1401_; 
v___x_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1401_, 0, v_e_1380_);
lean_ctor_set(v___x_1401_, 1, v___y_1386_);
return v___x_1401_;
}
case 4:
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_e_1380_);
lean_ctor_set(v___x_1402_, 1, v___y_1386_);
return v___x_1402_;
}
case 3:
{
lean_object* v___x_1403_; 
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v_e_1380_);
lean_ctor_set(v___x_1403_, 1, v___y_1386_);
return v___x_1403_;
}
default: 
{
lean_object* v___x_1404_; uint8_t v___x_1405_; 
v___x_1404_ = l_Lean_Expr_looseBVarRange(v_e_1380_);
v___x_1405_ = lean_nat_dec_le(v___x_1404_, v___x_1387_);
lean_dec(v___x_1404_);
if (v___x_1405_ == 0)
{
switch(lean_obj_tag(v_e_1380_))
{
case 9:
{
lean_object* v___x_1406_; 
v___x_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1406_, 0, v_e_1380_);
lean_ctor_set(v___x_1406_, 1, v___y_1386_);
return v___x_1406_;
}
case 2:
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v_e_1380_);
lean_ctor_set(v___x_1407_, 1, v___y_1386_);
return v___x_1407_;
}
case 0:
{
lean_object* v___x_1408_; 
v___x_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1408_, 0, v_e_1380_);
lean_ctor_set(v___x_1408_, 1, v___y_1386_);
return v___x_1408_;
}
case 1:
{
lean_object* v___x_1409_; 
v___x_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1409_, 0, v_e_1380_);
lean_ctor_set(v___x_1409_, 1, v___y_1386_);
return v___x_1409_;
}
case 4:
{
lean_object* v___x_1410_; 
v___x_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1410_, 0, v_e_1380_);
lean_ctor_set(v___x_1410_, 1, v___y_1386_);
return v___x_1410_;
}
case 3:
{
lean_object* v___x_1411_; 
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v_e_1380_);
lean_ctor_set(v___x_1411_, 1, v___y_1386_);
return v___x_1411_;
}
default: 
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___closed__1);
v___x_1413_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0(v_size_1381_, v_xs_1383_, v_e_1380_, v___x_1387_, v___x_1412_, v_debug_1384_, v___y_1385_, v___y_1386_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1423_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_a_1415_ = lean_ctor_get(v___x_1413_, 1);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1417_ = v___x_1413_;
v_isShared_1418_ = v_isSharedCheck_1423_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1423_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v_fst_1419_; lean_object* v___x_1421_; 
v_fst_1419_ = lean_ctor_get(v_a_1414_, 0);
lean_inc(v_fst_1419_);
lean_dec(v_a_1414_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v_fst_1419_);
v___x_1421_ = v___x_1417_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_fst_1419_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_a_1415_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
else
{
lean_object* v_a_1424_; lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
v_a_1424_ = lean_ctor_get(v___x_1413_, 0);
v_a_1425_ = lean_ctor_get(v___x_1413_, 1);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1413_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_inc(v_a_1424_);
lean_dec(v___x_1413_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1424_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
}
else
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1433_, 0, v_e_1380_);
lean_ctor_set(v___x_1433_, 1, v___y_1386_);
return v___x_1433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___boxed(lean_object* v_e_1434_, lean_object* v_size_1435_, lean_object* v___x_1436_, lean_object* v_xs_1437_, lean_object* v_debug_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
uint8_t v_debug_boxed_1441_; lean_object* v_res_1442_; 
v_debug_boxed_1441_ = lean_unbox(v_debug_1438_);
v_res_1442_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0(v_e_1434_, v_size_1435_, v___x_1436_, v_xs_1437_, v_debug_boxed_1441_, v___y_1439_, v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec_ref(v_xs_1437_);
lean_dec_ref(v___x_1436_);
lean_dec(v_size_1435_);
return v_res_1442_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__2(void){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1445_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_1446_ = lean_unsigned_to_nat(16u);
v___x_1447_ = lean_unsigned_to_nat(62u);
v___x_1448_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__1));
v___x_1449_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__0));
v___x_1450_ = l_mkPanicMessageWithDecl(v___x_1449_, v___x_1448_, v___x_1447_, v___x_1446_, v___x_1445_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(lean_object* v_e_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v_a_1462_; uint8_t v___x_1480_; 
v___x_1480_ = l_Lean_Expr_hasLooseBVars(v_e_1451_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; 
v___x_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1481_, 0, v_e_1451_);
return v___x_1481_;
}
else
{
lean_object* v___x_1482_; lean_object* v_subst_1483_; lean_object* v___x_1484_; 
v___x_1482_ = lean_st_ref_get(v_a_1453_);
v_subst_1483_ = lean_ctor_get(v___x_1482_, 2);
lean_inc_ref(v_subst_1483_);
lean_dec(v___x_1482_);
v___x_1484_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_subst_1483_, v_e_1451_);
lean_dec_ref(v_subst_1483_);
if (lean_obj_tag(v___x_1484_) == 1)
{
lean_object* v_val_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec_ref(v_e_1451_);
v_val_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_val_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set_tag(v___x_1487_, 0);
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_val_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v_xs_1495_; lean_object* v_size_1496_; uint8_t v_debug_1497_; lean_object* v_env_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___f_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_dec(v___x_1484_);
v___x_1493_ = lean_st_ref_get(v_a_1455_);
v___x_1494_ = lean_st_ref_get(v_a_1459_);
v_xs_1495_ = lean_ctor_get(v_a_1452_, 0);
v_size_1496_ = lean_ctor_get(v_xs_1495_, 2);
v_debug_1497_ = lean_ctor_get_uint8(v___x_1493_, sizeof(void*)*11);
lean_dec(v___x_1493_);
v_env_1498_ = lean_ctor_get(v___x_1494_, 0);
lean_inc_ref(v_env_1498_);
lean_dec(v___x_1494_);
v___x_1499_ = l_Lean_instInhabitedExpr;
v___x_1500_ = 0;
v___x_1501_ = lean_box(v_debug_1497_);
lean_inc_ref(v_xs_1495_);
lean_inc(v_size_1496_);
lean_inc_ref(v_e_1451_);
v___f_1502_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___lam__0___boxed), 7, 5);
lean_closure_set(v___f_1502_, 0, v_e_1451_);
lean_closure_set(v___f_1502_, 1, v_size_1496_);
lean_closure_set(v___f_1502_, 2, v___x_1499_);
lean_closure_set(v___f_1502_, 3, v_xs_1495_);
lean_closure_set(v___f_1502_, 4, v___x_1501_);
v___x_1503_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1503_, 0, v_env_1498_);
lean_ctor_set_uint8(v___x_1503_, sizeof(void*)*1, v___x_1500_);
lean_ctor_set_uint8(v___x_1503_, sizeof(void*)*1 + 1, v___x_1500_);
v___x_1504_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1502_, v___x_1503_, v_a_1455_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
lean_dec_ref_known(v___x_1504_, 1);
if (lean_obj_tag(v_a_1505_) == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec_ref_known(v_a_1505_, 1);
v___x_1506_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__2, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__2_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___closed__2);
v___x_1507_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__1(v___x_1506_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1508_);
lean_dec_ref_known(v___x_1507_, 1);
v_a_1462_ = v_a_1508_;
goto v___jp_1461_;
}
else
{
lean_dec_ref(v_e_1451_);
return v___x_1507_;
}
}
else
{
lean_object* v_a_1509_; 
v_a_1509_ = lean_ctor_get(v_a_1505_, 0);
lean_inc(v_a_1509_);
lean_dec_ref_known(v_a_1505_, 1);
v_a_1462_ = v_a_1509_;
goto v___jp_1461_;
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v_e_1451_);
v_a_1510_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1504_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1504_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
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
v___jp_1461_:
{
lean_object* v___x_1463_; lean_object* v_visited_1464_; lean_object* v_types_1465_; lean_object* v_subst_1466_; lean_object* v_visitedClosed_1467_; lean_object* v_hasDepLetCache_1468_; lean_object* v_numConverted_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1479_; 
v___x_1463_ = lean_st_ref_take(v_a_1453_);
v_visited_1464_ = lean_ctor_get(v___x_1463_, 0);
v_types_1465_ = lean_ctor_get(v___x_1463_, 1);
v_subst_1466_ = lean_ctor_get(v___x_1463_, 2);
v_visitedClosed_1467_ = lean_ctor_get(v___x_1463_, 3);
v_hasDepLetCache_1468_ = lean_ctor_get(v___x_1463_, 4);
v_numConverted_1469_ = lean_ctor_get(v___x_1463_, 5);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1471_ = v___x_1463_;
v_isShared_1472_ = v_isSharedCheck_1479_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_numConverted_1469_);
lean_inc(v_hasDepLetCache_1468_);
lean_inc(v_visitedClosed_1467_);
lean_inc(v_subst_1466_);
lean_inc(v_types_1465_);
lean_inc(v_visited_1464_);
lean_dec(v___x_1463_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1479_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1475_; 
lean_inc_ref(v_a_1462_);
v___x_1473_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_subst_1466_, v_e_1451_, v_a_1462_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 2, v___x_1473_);
v___x_1475_ = v___x_1471_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_visited_1464_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_types_1465_);
lean_ctor_set(v_reuseFailAlloc_1478_, 2, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1478_, 3, v_visitedClosed_1467_);
lean_ctor_set(v_reuseFailAlloc_1478_, 4, v_hasDepLetCache_1468_);
lean_ctor_set(v_reuseFailAlloc_1478_, 5, v_numConverted_1469_);
v___x_1475_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = lean_st_ref_put(v_a_1453_, v___x_1475_);
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v_a_1462_);
return v___x_1477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv___boxed(lean_object* v_e_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_e_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
lean_dec(v_a_1522_);
lean_dec_ref(v_a_1521_);
lean_dec(v_a_1520_);
lean_dec_ref(v_a_1519_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1529_, lean_object* v_m_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___redArg(v_m_1530_, v_a_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1533_, lean_object* v_m_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2(v_00_u03b2_1533_, v_m_1534_, v_a_1535_);
lean_dec_ref(v_a_1535_);
lean_dec_ref(v_m_1534_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_1537_, lean_object* v_a_1538_, lean_object* v_x_1539_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___redArg(v_a_1538_, v_x_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_1541_, lean_object* v_a_1542_, lean_object* v_x_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0_spec__0_spec__2_spec__10(v_00_u03b2_1541_, v_a_1542_, v_x_1543_);
lean_dec(v_x_1543_);
lean_dec_ref(v_a_1542_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(lean_object* v_msgData_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v___x_1551_; lean_object* v_env_1552_; lean_object* v___x_1553_; lean_object* v_mctx_1554_; lean_object* v_lctx_1555_; lean_object* v_options_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1551_ = lean_st_ref_get(v___y_1549_);
v_env_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc_ref(v_env_1552_);
lean_dec(v___x_1551_);
v___x_1553_ = lean_st_ref_get(v___y_1547_);
v_mctx_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc_ref(v_mctx_1554_);
lean_dec(v___x_1553_);
v_lctx_1555_ = lean_ctor_get(v___y_1546_, 2);
v_options_1556_ = lean_ctor_get(v___y_1548_, 1);
lean_inc_ref(v_options_1556_);
lean_inc_ref(v_lctx_1555_);
v___x_1557_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1557_, 0, v_env_1552_);
lean_ctor_set(v___x_1557_, 1, v_mctx_1554_);
lean_ctor_set(v___x_1557_, 2, v_lctx_1555_);
lean_ctor_set(v___x_1557_, 3, v_options_1556_);
v___x_1558_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
lean_ctor_set(v___x_1558_, 1, v_msgData_1545_);
v___x_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0___boxed(lean_object* v_msgData_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(v_msgData_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(lean_object* v_msg_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_ref_1573_; lean_object* v___x_1574_; lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1583_; 
v_ref_1573_ = lean_ctor_get(v___y_1570_, 4);
v___x_1574_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(v_msg_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1577_ = v___x_1574_;
v_isShared_1578_ = v_isSharedCheck_1583_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1574_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1583_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
lean_inc(v_ref_1573_);
v___x_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1579_, 0, v_ref_1573_);
lean_ctor_set(v___x_1579_, 1, v_a_1575_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set_tag(v___x_1577_, 1);
lean_ctor_set(v___x_1577_, 0, v___x_1579_);
v___x_1581_ = v___x_1577_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg___boxed(lean_object* v_msg_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v_msg_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
return v_res_1590_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__0));
v___x_1593_ = l_Lean_stringToMessageData(v___x_1592_);
return v___x_1593_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__2));
v___x_1596_ = l_Lean_stringToMessageData(v___x_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(lean_object* v_t_1597_, lean_object* v_s_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
size_t v___x_1608_; size_t v___x_1609_; uint8_t v___x_1610_; 
v___x_1608_ = lean_ptr_addr(v_t_1597_);
v___x_1609_ = lean_ptr_addr(v_s_1598_);
v___x_1610_ = lean_usize_dec_eq(v___x_1608_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; 
lean_inc_ref(v_s_1598_);
lean_inc_ref(v_t_1597_);
v___x_1611_ = l_Lean_Meta_isExprDefEq(v_t_1597_, v_s_1598_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1629_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1614_ = v___x_1611_;
v_isShared_1615_ = v_isSharedCheck_1629_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1629_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
uint8_t v___x_1616_; 
v___x_1616_ = lean_unbox(v_a_1612_);
lean_dec(v_a_1612_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
lean_del_object(v___x_1614_);
v___x_1617_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1);
v___x_1618_ = l_Lean_indentExpr(v_t_1597_);
v___x_1619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1617_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3);
v___x_1621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = l_Lean_indentExpr(v_s_1598_);
v___x_1623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v___x_1623_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1624_;
}
else
{
lean_object* v___x_1625_; lean_object* v___x_1627_; 
lean_dec_ref(v_s_1598_);
lean_dec_ref(v_t_1597_);
v___x_1625_ = lean_box(0);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v___x_1625_);
v___x_1627_ = v___x_1614_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec_ref(v_s_1598_);
lean_dec_ref(v_t_1597_);
v_a_1630_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1611_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1611_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_dec_ref(v_s_1598_);
lean_dec_ref(v_t_1597_);
v___x_1638_ = lean_box(0);
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
return v___x_1639_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___boxed(lean_object* v_t_1640_, lean_object* v_s_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_t_1640_, v_s_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0(lean_object* v_00_u03b1_1652_, lean_object* v_msg_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v_msg_1653_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___boxed(lean_object* v_00_u03b1_1664_, lean_object* v_msg_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0(v_00_u03b1_1664_, v_msg_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
return v_res_1675_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__0));
v___x_1678_ = l_Lean_stringToMessageData(v___x_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(lean_object* v_type_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
uint8_t v___x_1687_; 
v___x_1687_ = l_Lean_Expr_isForall(v_type_1679_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; 
lean_inc(v_a_1685_);
lean_inc_ref(v_a_1684_);
lean_inc(v_a_1683_);
lean_inc_ref(v_a_1682_);
v___x_1688_ = lean_whnf(v_type_1679_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; uint8_t v___x_1690_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1689_);
lean_dec_ref_known(v___x_1688_, 1);
v___x_1690_ = l_Lean_Expr_isForall(v_a_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
v___x_1691_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1);
v___x_1692_ = l_Lean_indentExpr(v_a_1689_);
v___x_1693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1691_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v___x_1693_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1694_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1694_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
else
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_Meta_Sym_shareCommon(v_a_1689_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
return v___x_1703_;
}
}
else
{
return v___x_1688_;
}
}
else
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1704_, 0, v_type_1679_);
return v___x_1704_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___boxed(lean_object* v_type_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_type_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall(lean_object* v_type_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_type_1714_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___boxed(lean_object* v_type_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall(v_type_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
lean_dec(v_a_1727_);
lean_dec_ref(v_a_1726_);
return v_res_1735_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_isClean(lean_object* v_e_1736_, lean_object* v_ctx_1737_){
_start:
{
lean_object* v_cleanSuffix_1738_; lean_object* v___x_1739_; uint8_t v___x_1740_; 
v_cleanSuffix_1738_ = lean_ctor_get(v_ctx_1737_, 2);
v___x_1739_ = l_Lean_Expr_looseBVarRange(v_e_1736_);
v___x_1740_ = lean_nat_dec_le(v___x_1739_, v_cleanSuffix_1738_);
lean_dec(v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_isClean___boxed(lean_object* v_e_1741_, lean_object* v_ctx_1742_){
_start:
{
uint8_t v_res_1743_; lean_object* v_r_1744_; 
v_res_1743_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_isClean(v_e_1741_, v_ctx_1742_);
lean_dec_ref(v_ctx_1742_);
lean_dec_ref(v_e_1741_);
v_r_1744_ = lean_box(v_res_1743_);
return v_r_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(lean_object* v_e_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_e_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v_keyedConfig_1757_; uint8_t v_trackZetaDelta_1758_; lean_object* v_zetaDeltaSet_1759_; lean_object* v_lctx_1760_; lean_object* v_localInstances_1761_; lean_object* v_defEqCtx_x3f_1762_; lean_object* v_synthPendingDepth_1763_; lean_object* v_customCanUnfoldPredicate_x3f_1764_; uint8_t v_univApprox_1765_; uint8_t v_inTypeClassResolution_1766_; uint8_t v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref_known(v___x_1755_, 1);
v_keyedConfig_1757_ = lean_ctor_get(v_a_1750_, 0);
v_trackZetaDelta_1758_ = lean_ctor_get_uint8(v_a_1750_, sizeof(void*)*7);
v_zetaDeltaSet_1759_ = lean_ctor_get(v_a_1750_, 1);
v_lctx_1760_ = lean_ctor_get(v_a_1750_, 2);
v_localInstances_1761_ = lean_ctor_get(v_a_1750_, 3);
v_defEqCtx_x3f_1762_ = lean_ctor_get(v_a_1750_, 4);
v_synthPendingDepth_1763_ = lean_ctor_get(v_a_1750_, 5);
v_customCanUnfoldPredicate_x3f_1764_ = lean_ctor_get(v_a_1750_, 6);
v_univApprox_1765_ = lean_ctor_get_uint8(v_a_1750_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1766_ = lean_ctor_get_uint8(v_a_1750_, sizeof(void*)*7 + 2);
v___x_1767_ = 0;
lean_inc(v_customCanUnfoldPredicate_x3f_1764_);
lean_inc(v_synthPendingDepth_1763_);
lean_inc(v_defEqCtx_x3f_1762_);
lean_inc_ref(v_localInstances_1761_);
lean_inc_ref(v_lctx_1760_);
lean_inc(v_zetaDeltaSet_1759_);
lean_inc_ref(v_keyedConfig_1757_);
v___x_1768_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1768_, 0, v_keyedConfig_1757_);
lean_ctor_set(v___x_1768_, 1, v_zetaDeltaSet_1759_);
lean_ctor_set(v___x_1768_, 2, v_lctx_1760_);
lean_ctor_set(v___x_1768_, 3, v_localInstances_1761_);
lean_ctor_set(v___x_1768_, 4, v_defEqCtx_x3f_1762_);
lean_ctor_set(v___x_1768_, 5, v_synthPendingDepth_1763_);
lean_ctor_set(v___x_1768_, 6, v_customCanUnfoldPredicate_x3f_1764_);
lean_ctor_set_uint8(v___x_1768_, sizeof(void*)*7, v_trackZetaDelta_1758_);
lean_ctor_set_uint8(v___x_1768_, sizeof(void*)*7 + 1, v_univApprox_1765_);
lean_ctor_set_uint8(v___x_1768_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1766_);
lean_ctor_set_uint8(v___x_1768_, sizeof(void*)*7 + 3, v___x_1767_);
lean_inc(v_a_1753_);
lean_inc_ref(v_a_1752_);
lean_inc(v_a_1751_);
v___x_1769_ = lean_infer_type(v_a_1756_, v___x_1768_, v_a_1751_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1771_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref_known(v___x_1769_, 1);
v___x_1771_ = l_Lean_Meta_Sym_shareCommon(v_a_1770_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
return v___x_1771_;
}
else
{
return v___x_1769_;
}
}
else
{
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback___boxed(lean_object* v_e_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(v_e_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
lean_dec(v_a_1778_);
lean_dec_ref(v_a_1777_);
lean_dec(v_a_1776_);
lean_dec_ref(v_a_1775_);
lean_dec(v_a_1774_);
lean_dec_ref(v_a_1773_);
return v_res_1782_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_instMonadEIO(lean_box(0));
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(lean_object* v_msg_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v_toApplicative_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1865_; 
v___x_1798_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0);
v___x_1799_ = l_StateRefT_x27_instMonad___redArg(v___x_1798_);
v_toApplicative_1800_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1865_ == 0)
{
lean_object* v_unused_1866_; 
v_unused_1866_ = lean_ctor_get(v___x_1799_, 1);
lean_dec(v_unused_1866_);
v___x_1802_ = v___x_1799_;
v_isShared_1803_ = v_isSharedCheck_1865_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_toApplicative_1800_);
lean_dec(v___x_1799_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1865_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v_toFunctor_1804_; lean_object* v_toSeq_1805_; lean_object* v_toSeqLeft_1806_; lean_object* v_toSeqRight_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1863_; 
v_toFunctor_1804_ = lean_ctor_get(v_toApplicative_1800_, 0);
v_toSeq_1805_ = lean_ctor_get(v_toApplicative_1800_, 2);
v_toSeqLeft_1806_ = lean_ctor_get(v_toApplicative_1800_, 3);
v_toSeqRight_1807_ = lean_ctor_get(v_toApplicative_1800_, 4);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_toApplicative_1800_);
if (v_isSharedCheck_1863_ == 0)
{
lean_object* v_unused_1864_; 
v_unused_1864_ = lean_ctor_get(v_toApplicative_1800_, 1);
lean_dec(v_unused_1864_);
v___x_1809_ = v_toApplicative_1800_;
v_isShared_1810_ = v_isSharedCheck_1863_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_toSeqRight_1807_);
lean_inc(v_toSeqLeft_1806_);
lean_inc(v_toSeq_1805_);
lean_inc(v_toFunctor_1804_);
lean_dec(v_toApplicative_1800_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1863_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___f_1811_; lean_object* v___f_1812_; lean_object* v___f_1813_; lean_object* v___f_1814_; lean_object* v___x_1815_; lean_object* v___f_1816_; lean_object* v___f_1817_; lean_object* v___f_1818_; lean_object* v___x_1820_; 
v___f_1811_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__1));
v___f_1812_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1804_);
v___f_1813_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1813_, 0, v_toFunctor_1804_);
v___f_1814_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1814_, 0, v_toFunctor_1804_);
v___x_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___f_1813_);
lean_ctor_set(v___x_1815_, 1, v___f_1814_);
v___f_1816_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1816_, 0, v_toSeqRight_1807_);
v___f_1817_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1817_, 0, v_toSeqLeft_1806_);
v___f_1818_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1818_, 0, v_toSeq_1805_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 4, v___f_1816_);
lean_ctor_set(v___x_1809_, 3, v___f_1817_);
lean_ctor_set(v___x_1809_, 2, v___f_1818_);
lean_ctor_set(v___x_1809_, 1, v___f_1811_);
lean_ctor_set(v___x_1809_, 0, v___x_1815_);
v___x_1820_ = v___x_1809_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1815_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v___f_1811_);
lean_ctor_set(v_reuseFailAlloc_1862_, 2, v___f_1818_);
lean_ctor_set(v_reuseFailAlloc_1862_, 3, v___f_1817_);
lean_ctor_set(v_reuseFailAlloc_1862_, 4, v___f_1816_);
v___x_1820_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1822_; 
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 1, v___f_1812_);
lean_ctor_set(v___x_1802_, 0, v___x_1820_);
v___x_1822_ = v___x_1802_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1820_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v___f_1812_);
v___x_1822_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1823_; lean_object* v_toApplicative_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1859_; 
v___x_1823_ = l_StateRefT_x27_instMonad___redArg(v___x_1822_);
v_toApplicative_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; 
v_unused_1860_ = lean_ctor_get(v___x_1823_, 1);
lean_dec(v_unused_1860_);
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1859_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_toApplicative_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1859_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v_toFunctor_1828_; lean_object* v_toSeq_1829_; lean_object* v_toSeqLeft_1830_; lean_object* v_toSeqRight_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1857_; 
v_toFunctor_1828_ = lean_ctor_get(v_toApplicative_1824_, 0);
v_toSeq_1829_ = lean_ctor_get(v_toApplicative_1824_, 2);
v_toSeqLeft_1830_ = lean_ctor_get(v_toApplicative_1824_, 3);
v_toSeqRight_1831_ = lean_ctor_get(v_toApplicative_1824_, 4);
v_isSharedCheck_1857_ = !lean_is_exclusive(v_toApplicative_1824_);
if (v_isSharedCheck_1857_ == 0)
{
lean_object* v_unused_1858_; 
v_unused_1858_ = lean_ctor_get(v_toApplicative_1824_, 1);
lean_dec(v_unused_1858_);
v___x_1833_ = v_toApplicative_1824_;
v_isShared_1834_ = v_isSharedCheck_1857_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_toSeqRight_1831_);
lean_inc(v_toSeqLeft_1830_);
lean_inc(v_toSeq_1829_);
lean_inc(v_toFunctor_1828_);
lean_dec(v_toApplicative_1824_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1857_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___f_1835_; lean_object* v___f_1836_; lean_object* v___f_1837_; lean_object* v___f_1838_; lean_object* v___x_1839_; lean_object* v___f_1840_; lean_object* v___f_1841_; lean_object* v___f_1842_; lean_object* v___x_1844_; 
v___f_1835_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__3));
v___f_1836_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1828_);
v___f_1837_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1837_, 0, v_toFunctor_1828_);
v___f_1838_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1838_, 0, v_toFunctor_1828_);
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___f_1837_);
lean_ctor_set(v___x_1839_, 1, v___f_1838_);
v___f_1840_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1840_, 0, v_toSeqRight_1831_);
v___f_1841_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1841_, 0, v_toSeqLeft_1830_);
v___f_1842_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1842_, 0, v_toSeq_1829_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 4, v___f_1840_);
lean_ctor_set(v___x_1833_, 3, v___f_1841_);
lean_ctor_set(v___x_1833_, 2, v___f_1842_);
lean_ctor_set(v___x_1833_, 1, v___f_1835_);
lean_ctor_set(v___x_1833_, 0, v___x_1839_);
v___x_1844_ = v___x_1833_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v___f_1835_);
lean_ctor_set(v_reuseFailAlloc_1856_, 2, v___f_1842_);
lean_ctor_set(v_reuseFailAlloc_1856_, 3, v___f_1841_);
lean_ctor_set(v_reuseFailAlloc_1856_, 4, v___f_1840_);
v___x_1844_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1846_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 1, v___f_1836_);
lean_ctor_set(v___x_1826_, 0, v___x_1844_);
v___x_1846_ = v___x_1826_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1844_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v___f_1836_);
v___x_1846_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___f_1852_; lean_object* v___x_11696__overap_1853_; lean_object* v___x_1854_; 
v___x_1847_ = l_StateRefT_x27_instMonad___redArg(v___x_1846_);
v___x_1848_ = l_ReaderT_instMonad___redArg(v___x_1847_);
v___x_1849_ = l_StateRefT_x27_instMonad___redArg(v___x_1848_);
v___x_1850_ = l_Lean_instInhabitedExpr;
v___x_1851_ = l_instInhabitedOfMonad___redArg(v___x_1849_, v___x_1850_);
v___f_1852_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1852_, 0, v___x_1851_);
v___x_11696__overap_1853_ = lean_panic_fn_borrowed(v___f_1852_, v_msg_1788_);
lean_dec_ref(v___f_1852_);
lean_inc(v___y_1796_);
lean_inc_ref(v___y_1795_);
lean_inc(v___y_1794_);
lean_inc_ref(v___y_1793_);
lean_inc(v___y_1792_);
lean_inc_ref(v___y_1791_);
lean_inc(v___y_1790_);
lean_inc_ref(v___y_1789_);
v___x_1854_ = lean_apply_9(v___x_11696__overap_1853_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, lean_box(0));
return v___x_1854_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___boxed(lean_object* v_msg_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(v_msg_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
return v_res_1877_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1880_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_1881_ = lean_unsigned_to_nat(44u);
v___x_1882_ = lean_unsigned_to_nat(367u);
v___x_1883_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__1));
v___x_1884_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0));
v___x_1885_ = l_mkPanicMessageWithDecl(v___x_1884_, v___x_1883_, v___x_1882_, v___x_1881_, v___x_1880_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(lean_object* v_e_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v_type_1897_; lean_object* v___y_1898_; uint8_t v___x_1916_; 
v___x_1916_ = l_Lean_Expr_hasLooseBVars(v_e_1886_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_Meta_Sym_inferType(v_e_1886_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
return v___x_1917_;
}
else
{
lean_object* v___x_1918_; lean_object* v___y_1920_; lean_object* v_types_1924_; lean_object* v___x_1925_; 
v___x_1918_ = lean_st_ref_get(v_a_1888_);
v_types_1924_ = lean_ctor_get(v___x_1918_, 1);
lean_inc_ref(v_types_1924_);
lean_dec(v___x_1918_);
v___x_1925_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_types_1924_, v_e_1886_);
lean_dec_ref(v_types_1924_);
if (lean_obj_tag(v___x_1925_) == 1)
{
lean_object* v_val_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec_ref(v_e_1886_);
v_val_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_val_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
lean_ctor_set_tag(v___x_1928_, 0);
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_val_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
else
{
lean_dec(v___x_1925_);
switch(lean_obj_tag(v_e_1886_))
{
case 0:
{
lean_object* v_xs_1934_; lean_object* v_deBruijnIndex_1935_; lean_object* v_size_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; 
v_xs_1934_ = lean_ctor_get(v_a_1887_, 0);
v_deBruijnIndex_1935_ = lean_ctor_get(v_e_1886_, 0);
v_size_1936_ = lean_ctor_get(v_xs_1934_, 2);
v___x_1937_ = l_Lean_instInhabitedExpr;
v___x_1938_ = lean_nat_sub(v_size_1936_, v_deBruijnIndex_1935_);
v___x_1939_ = lean_unsigned_to_nat(1u);
v___x_1940_ = lean_nat_sub(v___x_1938_, v___x_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_nat_dec_lt(v___x_1940_, v_size_1936_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; 
lean_dec(v___x_1940_);
v___x_1942_ = l_outOfBounds___redArg(v___x_1937_);
v___y_1920_ = v___x_1942_;
goto v___jp_1919_;
}
else
{
lean_object* v___x_1943_; 
v___x_1943_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1937_, v_xs_1934_, v___x_1940_);
lean_dec(v___x_1940_);
v___y_1920_ = v___x_1943_;
goto v___jp_1919_;
}
}
case 10:
{
lean_object* v_expr_1944_; lean_object* v___x_1945_; 
v_expr_1944_ = lean_ctor_get(v_e_1886_, 1);
lean_inc_ref(v_expr_1944_);
v___x_1945_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_expr_1944_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref_known(v___x_1945_, 1);
v_type_1897_ = v_a_1946_;
v___y_1898_ = v_a_1888_;
goto v___jp_1896_;
}
else
{
lean_dec_ref_known(v_e_1886_, 2);
return v___x_1945_;
}
}
case 5:
{
lean_object* v_fn_1947_; lean_object* v_arg_1948_; lean_object* v___x_1949_; 
v_fn_1947_ = lean_ctor_get(v_e_1886_, 0);
v_arg_1948_ = lean_ctor_get(v_e_1886_, 1);
lean_inc_ref(v_fn_1947_);
v___x_1949_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_fn_1947_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v___x_1951_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref_known(v___x_1949_, 1);
v___x_1951_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_a_1950_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
if (lean_obj_tag(v_a_1952_) == 7)
{
lean_object* v_body_1953_; uint8_t v___x_1954_; 
v_body_1953_ = lean_ctor_get(v_a_1952_, 2);
lean_inc_ref(v_body_1953_);
lean_dec_ref_known(v_a_1952_, 3);
v___x_1954_ = l_Lean_Expr_hasLooseBVars(v_body_1953_);
if (v___x_1954_ == 0)
{
v_type_1897_ = v_body_1953_;
v___y_1898_ = v_a_1888_;
goto v___jp_1896_;
}
else
{
lean_object* v___x_1955_; 
lean_inc_ref(v_arg_1948_);
v___x_1955_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_arg_1948_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1956_);
lean_dec_ref_known(v___x_1955_, 1);
v___x_1957_ = lean_expr_instantiate1(v_body_1953_, v_a_1956_);
lean_dec(v_a_1956_);
lean_dec_ref(v_body_1953_);
v___x_1958_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1957_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1958_, 1);
v_type_1897_ = v_a_1959_;
v___y_1898_ = v_a_1888_;
goto v___jp_1896_;
}
else
{
lean_dec_ref_known(v_e_1886_, 2);
return v___x_1958_;
}
}
else
{
lean_dec_ref(v_body_1953_);
lean_dec_ref_known(v_e_1886_, 2);
return v___x_1955_;
}
}
}
else
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
lean_dec(v_a_1952_);
v___x_1960_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2);
v___x_1961_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(v___x_1960_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1962_);
lean_dec_ref_known(v___x_1961_, 1);
v_type_1897_ = v_a_1962_;
v___y_1898_ = v_a_1888_;
goto v___jp_1896_;
}
else
{
lean_dec_ref_known(v_e_1886_, 2);
return v___x_1961_;
}
}
}
else
{
lean_dec_ref_known(v_e_1886_, 2);
return v___x_1951_;
}
}
else
{
lean_dec_ref_known(v_e_1886_, 2);
return v___x_1949_;
}
}
default: 
{
lean_object* v___x_1963_; 
lean_inc_ref(v_e_1886_);
v___x_1963_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(v_e_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_1964_);
lean_dec_ref_known(v___x_1963_, 1);
v_type_1897_ = v_a_1964_;
v___y_1898_ = v_a_1888_;
goto v___jp_1896_;
}
else
{
lean_dec_ref(v_e_1886_);
return v___x_1963_;
}
}
}
}
v___jp_1919_:
{
lean_object* v_lctx_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v_lctx_1921_ = lean_ctor_get(v_a_1891_, 2);
lean_inc_ref(v_lctx_1921_);
v___x_1922_ = l_Lean_LocalContext_getFVar_x21(v_lctx_1921_, v___y_1920_);
lean_dec_ref(v___y_1920_);
v___x_1923_ = l_Lean_LocalDecl_type(v___x_1922_);
lean_dec_ref(v___x_1922_);
v_type_1897_ = v___x_1923_;
v___y_1898_ = v_a_1888_;
goto v___jp_1896_;
}
}
v___jp_1896_:
{
lean_object* v___x_1899_; lean_object* v_visited_1900_; lean_object* v_types_1901_; lean_object* v_subst_1902_; lean_object* v_visitedClosed_1903_; lean_object* v_hasDepLetCache_1904_; lean_object* v_numConverted_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1915_; 
v___x_1899_ = lean_st_ref_take(v___y_1898_);
v_visited_1900_ = lean_ctor_get(v___x_1899_, 0);
v_types_1901_ = lean_ctor_get(v___x_1899_, 1);
v_subst_1902_ = lean_ctor_get(v___x_1899_, 2);
v_visitedClosed_1903_ = lean_ctor_get(v___x_1899_, 3);
v_hasDepLetCache_1904_ = lean_ctor_get(v___x_1899_, 4);
v_numConverted_1905_ = lean_ctor_get(v___x_1899_, 5);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1907_ = v___x_1899_;
v_isShared_1908_ = v_isSharedCheck_1915_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_numConverted_1905_);
lean_inc(v_hasDepLetCache_1904_);
lean_inc(v_visitedClosed_1903_);
lean_inc(v_subst_1902_);
lean_inc(v_types_1901_);
lean_inc(v_visited_1900_);
lean_dec(v___x_1899_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1915_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
lean_inc_ref(v_type_1897_);
v___x_1909_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_types_1901_, v_e_1886_, v_type_1897_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 1, v___x_1909_);
v___x_1911_ = v___x_1907_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_visited_1900_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1914_, 2, v_subst_1902_);
lean_ctor_set(v_reuseFailAlloc_1914_, 3, v_visitedClosed_1903_);
lean_ctor_set(v_reuseFailAlloc_1914_, 4, v_hasDepLetCache_1904_);
lean_ctor_set(v_reuseFailAlloc_1914_, 5, v_numConverted_1905_);
v___x_1911_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_st_ref_put(v___y_1898_, v___x_1911_);
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v_type_1897_);
return v___x_1913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___boxed(lean_object* v_e_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_e_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(lean_object* v_fvarId_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = l_Lean_Expr_fvar___override(v_fvarId_1976_);
v___x_1980_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1979_, v___y_1977_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg___boxed(lean_object* v_fvarId_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(v_fvarId_1981_, v___y_1982_);
lean_dec(v___y_1982_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1(lean_object* v_fvarId_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(v_fvarId_1985_, v___y_1989_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___boxed(lean_object* v_fvarId_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1(v_fvarId_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0(lean_object* v_x_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v___x_2017_; 
lean_inc(v___y_2011_);
lean_inc_ref(v___y_2010_);
lean_inc(v___y_2009_);
lean_inc_ref(v___y_2008_);
v___x_2017_ = lean_apply_9(v_x_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, lean_box(0));
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0___boxed(lean_object* v_x_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0(v_x_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(lean_object* v_lctx_2029_, lean_object* v_localInsts_2030_, lean_object* v_x_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v___f_2041_; lean_object* v___x_2042_; 
lean_inc(v___y_2035_);
lean_inc_ref(v___y_2034_);
lean_inc(v___y_2033_);
lean_inc_ref(v___y_2032_);
v___f_2041_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2041_, 0, v_x_2031_);
lean_closure_set(v___f_2041_, 1, v___y_2032_);
lean_closure_set(v___f_2041_, 2, v___y_2033_);
lean_closure_set(v___f_2041_, 3, v___y_2034_);
lean_closure_set(v___f_2041_, 4, v___y_2035_);
v___x_2042_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2029_, v_localInsts_2030_, v___f_2041_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
if (lean_obj_tag(v___x_2042_) == 0)
{
return v___x_2042_;
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2042_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___boxed(lean_object* v_lctx_2051_, lean_object* v_localInsts_2052_, lean_object* v_x_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(v_lctx_2051_, v_localInsts_2052_, v_x_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2(lean_object* v_00_u03b1_2064_, lean_object* v_lctx_2065_, lean_object* v_localInsts_2066_, lean_object* v_x_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(v_lctx_2065_, v_localInsts_2066_, v_x_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___boxed(lean_object* v_00_u03b1_2078_, lean_object* v_lctx_2079_, lean_object* v_localInsts_2080_, lean_object* v_x_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2(v_00_u03b1_2078_, v_lctx_2079_, v_localInsts_2080_, v_x_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(lean_object* v___y_2092_, lean_object* v_visited_2093_, lean_object* v_types_2094_, lean_object* v_subst_2095_, lean_object* v_a_x3f_2096_){
_start:
{
lean_object* v___x_2098_; lean_object* v_visitedClosed_2099_; lean_object* v_hasDepLetCache_2100_; lean_object* v_numConverted_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2111_; 
v___x_2098_ = lean_st_ref_take(v___y_2092_);
v_visitedClosed_2099_ = lean_ctor_get(v___x_2098_, 3);
v_hasDepLetCache_2100_ = lean_ctor_get(v___x_2098_, 4);
v_numConverted_2101_ = lean_ctor_get(v___x_2098_, 5);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2111_ == 0)
{
lean_object* v_unused_2112_; lean_object* v_unused_2113_; lean_object* v_unused_2114_; 
v_unused_2112_ = lean_ctor_get(v___x_2098_, 2);
lean_dec(v_unused_2112_);
v_unused_2113_ = lean_ctor_get(v___x_2098_, 1);
lean_dec(v_unused_2113_);
v_unused_2114_ = lean_ctor_get(v___x_2098_, 0);
lean_dec(v_unused_2114_);
v___x_2103_ = v___x_2098_;
v_isShared_2104_ = v_isSharedCheck_2111_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_numConverted_2101_);
lean_inc(v_hasDepLetCache_2100_);
lean_inc(v_visitedClosed_2099_);
lean_dec(v___x_2098_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2111_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 2, v_subst_2095_);
lean_ctor_set(v___x_2103_, 1, v_types_2094_);
lean_ctor_set(v___x_2103_, 0, v_visited_2093_);
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_visited_2093_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_types_2094_);
lean_ctor_set(v_reuseFailAlloc_2110_, 2, v_subst_2095_);
lean_ctor_set(v_reuseFailAlloc_2110_, 3, v_visitedClosed_2099_);
lean_ctor_set(v_reuseFailAlloc_2110_, 4, v_hasDepLetCache_2100_);
lean_ctor_set(v_reuseFailAlloc_2110_, 5, v_numConverted_2101_);
v___x_2106_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2107_ = lean_st_ref_put(v___y_2092_, v___x_2106_);
v___x_2108_ = lean_box(0);
v___x_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
return v___x_2109_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0___boxed(lean_object* v___y_2115_, lean_object* v_visited_2116_, lean_object* v_types_2117_, lean_object* v_subst_2118_, lean_object* v_a_x3f_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(v___y_2115_, v_visited_2116_, v_types_2117_, v_subst_2118_, v_a_x3f_2119_);
lean_dec(v_a_x3f_2119_);
lean_dec(v___y_2115_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1(lean_object* v_k_2122_, lean_object* v_a_2123_, uint8_t v_tainted_2124_, uint8_t v_isCandidate_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v___y_2136_; lean_object* v_xs_2182_; lean_object* v_numCandidates_2183_; lean_object* v_cleanSuffix_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2203_; 
v_xs_2182_ = lean_ctor_get(v___y_2126_, 0);
v_numCandidates_2183_ = lean_ctor_get(v___y_2126_, 1);
v_cleanSuffix_2184_ = lean_ctor_get(v___y_2126_, 2);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___y_2126_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2186_ = v___y_2126_;
v_isShared_2187_ = v_isSharedCheck_2203_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_cleanSuffix_2184_);
lean_inc(v_numCandidates_2183_);
lean_inc(v_xs_2182_);
lean_dec(v___y_2126_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2203_;
goto v_resetjp_2185_;
}
v___jp_2135_:
{
lean_object* v___x_2137_; lean_object* v_visited_2138_; lean_object* v_types_2139_; lean_object* v_subst_2140_; lean_object* v_visitedClosed_2141_; lean_object* v_hasDepLetCache_2142_; lean_object* v_numConverted_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2181_; 
v___x_2137_ = lean_st_ref_take(v___y_2127_);
v_visited_2138_ = lean_ctor_get(v___x_2137_, 0);
v_types_2139_ = lean_ctor_get(v___x_2137_, 1);
v_subst_2140_ = lean_ctor_get(v___x_2137_, 2);
v_visitedClosed_2141_ = lean_ctor_get(v___x_2137_, 3);
v_hasDepLetCache_2142_ = lean_ctor_get(v___x_2137_, 4);
v_numConverted_2143_ = lean_ctor_get(v___x_2137_, 5);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2145_ = v___x_2137_;
v_isShared_2146_ = v_isSharedCheck_2181_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_numConverted_2143_);
lean_inc(v_hasDepLetCache_2142_);
lean_inc(v_visitedClosed_2141_);
lean_inc(v_subst_2140_);
lean_inc(v_types_2139_);
lean_inc(v_visited_2138_);
lean_dec(v___x_2137_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2181_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2147_; lean_object* v___x_2149_; 
v___x_2147_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 2, v___x_2147_);
lean_ctor_set(v___x_2145_, 1, v___x_2147_);
lean_ctor_set(v___x_2145_, 0, v___x_2147_);
v___x_2149_ = v___x_2145_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2180_, 2, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2180_, 3, v_visitedClosed_2141_);
lean_ctor_set(v_reuseFailAlloc_2180_, 4, v_hasDepLetCache_2142_);
lean_ctor_set(v_reuseFailAlloc_2180_, 5, v_numConverted_2143_);
v___x_2149_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2150_; lean_object* v_r_2151_; 
v___x_2150_ = lean_st_ref_put(v___y_2127_, v___x_2149_);
lean_inc(v___y_2133_);
lean_inc_ref(v___y_2132_);
lean_inc(v___y_2131_);
lean_inc_ref(v___y_2130_);
lean_inc(v___y_2129_);
lean_inc_ref(v___y_2128_);
lean_inc(v___y_2127_);
v_r_2151_ = lean_apply_10(v_k_2122_, v_a_2123_, v___y_2136_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, lean_box(0));
if (lean_obj_tag(v_r_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2168_; 
v_a_2152_ = lean_ctor_get(v_r_2151_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_r_2151_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2154_ = v_r_2151_;
v_isShared_2155_ = v_isSharedCheck_2168_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v_r_2151_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2168_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
lean_inc(v_a_2152_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set_tag(v___x_2154_, 1);
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
lean_object* v___x_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
v___x_2158_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(v___y_2127_, v_visited_2138_, v_types_2139_, v_subst_2140_, v___x_2157_);
lean_dec_ref(v___x_2157_);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2165_ == 0)
{
lean_object* v_unused_2166_; 
v_unused_2166_ = lean_ctor_get(v___x_2158_, 0);
lean_dec(v_unused_2166_);
v___x_2160_ = v___x_2158_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_dec(v___x_2158_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v_a_2152_);
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2152_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
v_a_2169_ = lean_ctor_get(v_r_2151_, 0);
lean_inc(v_a_2169_);
lean_dec_ref_known(v_r_2151_, 1);
v___x_2170_ = lean_box(0);
v___x_2171_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(v___y_2127_, v_visited_2138_, v_types_2139_, v_subst_2140_, v___x_2170_);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2178_ == 0)
{
lean_object* v_unused_2179_; 
v_unused_2179_ = lean_ctor_get(v___x_2171_, 0);
lean_dec(v_unused_2179_);
v___x_2173_ = v___x_2171_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_dec(v___x_2171_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
lean_ctor_set_tag(v___x_2173_, 1);
lean_ctor_set(v___x_2173_, 0, v_a_2169_);
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2169_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; lean_object* v___y_2190_; 
lean_inc_ref(v_a_2123_);
v___x_2188_ = l_Lean_PersistentArray_push___redArg(v_xs_2182_, v_a_2123_);
if (v_isCandidate_2125_ == 0)
{
lean_object* v___x_2201_; 
v___x_2201_ = lean_unsigned_to_nat(0u);
v___y_2190_ = v___x_2201_;
goto v___jp_2189_;
}
else
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_unsigned_to_nat(1u);
v___y_2190_ = v___x_2202_;
goto v___jp_2189_;
}
v___jp_2189_:
{
lean_object* v___x_2191_; 
v___x_2191_ = lean_nat_add(v_numCandidates_2183_, v___y_2190_);
lean_dec(v_numCandidates_2183_);
if (v_tainted_2124_ == 0)
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2192_ = lean_unsigned_to_nat(1u);
v___x_2193_ = lean_nat_add(v_cleanSuffix_2184_, v___x_2192_);
lean_dec(v_cleanSuffix_2184_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 2, v___x_2193_);
lean_ctor_set(v___x_2186_, 1, v___x_2191_);
lean_ctor_set(v___x_2186_, 0, v___x_2188_);
v___x_2195_ = v___x_2186_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2188_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2196_, 2, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
v___y_2136_ = v___x_2195_;
goto v___jp_2135_;
}
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2199_; 
lean_dec(v_cleanSuffix_2184_);
v___x_2197_ = lean_unsigned_to_nat(0u);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 2, v___x_2197_);
lean_ctor_set(v___x_2186_, 1, v___x_2191_);
lean_ctor_set(v___x_2186_, 0, v___x_2188_);
v___x_2199_ = v___x_2186_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2188_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2200_, 2, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
v___y_2136_ = v___x_2199_;
goto v___jp_2135_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1___boxed(lean_object* v_k_2204_, lean_object* v_a_2205_, lean_object* v_tainted_2206_, lean_object* v_isCandidate_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
uint8_t v_tainted_boxed_2217_; uint8_t v_isCandidate_boxed_2218_; lean_object* v_res_2219_; 
v_tainted_boxed_2217_ = lean_unbox(v_tainted_2206_);
v_isCandidate_boxed_2218_ = lean_unbox(v_isCandidate_2207_);
v_res_2219_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1(v_k_2204_, v_a_2205_, v_tainted_boxed_2217_, v_isCandidate_boxed_2218_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg(lean_object* v___y_2220_){
_start:
{
lean_object* v___x_2222_; lean_object* v_ngen_2223_; lean_object* v_namePrefix_2224_; lean_object* v_idx_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2254_; 
v___x_2222_ = lean_st_ref_get(v___y_2220_);
v_ngen_2223_ = lean_ctor_get(v___x_2222_, 2);
lean_inc_ref(v_ngen_2223_);
lean_dec(v___x_2222_);
v_namePrefix_2224_ = lean_ctor_get(v_ngen_2223_, 0);
v_idx_2225_ = lean_ctor_get(v_ngen_2223_, 1);
v_isSharedCheck_2254_ = !lean_is_exclusive(v_ngen_2223_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2227_ = v_ngen_2223_;
v_isShared_2228_ = v_isSharedCheck_2254_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_idx_2225_);
lean_inc(v_namePrefix_2224_);
lean_dec(v_ngen_2223_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2254_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v_env_2230_; lean_object* v_nextMacroScope_2231_; lean_object* v_auxDeclNGen_2232_; lean_object* v_traceState_2233_; lean_object* v_cache_2234_; lean_object* v_messages_2235_; lean_object* v_infoState_2236_; lean_object* v_snapshotTasks_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2252_; 
v___x_2229_ = lean_st_ref_take(v___y_2220_);
v_env_2230_ = lean_ctor_get(v___x_2229_, 0);
v_nextMacroScope_2231_ = lean_ctor_get(v___x_2229_, 1);
v_auxDeclNGen_2232_ = lean_ctor_get(v___x_2229_, 3);
v_traceState_2233_ = lean_ctor_get(v___x_2229_, 4);
v_cache_2234_ = lean_ctor_get(v___x_2229_, 5);
v_messages_2235_ = lean_ctor_get(v___x_2229_, 6);
v_infoState_2236_ = lean_ctor_get(v___x_2229_, 7);
v_snapshotTasks_2237_ = lean_ctor_get(v___x_2229_, 8);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2252_ == 0)
{
lean_object* v_unused_2253_; 
v_unused_2253_ = lean_ctor_get(v___x_2229_, 2);
lean_dec(v_unused_2253_);
v___x_2239_ = v___x_2229_;
v_isShared_2240_ = v_isSharedCheck_2252_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_snapshotTasks_2237_);
lean_inc(v_infoState_2236_);
lean_inc(v_messages_2235_);
lean_inc(v_cache_2234_);
lean_inc(v_traceState_2233_);
lean_inc(v_auxDeclNGen_2232_);
lean_inc(v_nextMacroScope_2231_);
lean_inc(v_env_2230_);
lean_dec(v___x_2229_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2252_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v_r_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2245_; 
lean_inc(v_idx_2225_);
lean_inc(v_namePrefix_2224_);
v_r_2241_ = l_Lean_Name_num___override(v_namePrefix_2224_, v_idx_2225_);
v___x_2242_ = lean_unsigned_to_nat(1u);
v___x_2243_ = lean_nat_add(v_idx_2225_, v___x_2242_);
lean_dec(v_idx_2225_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 1, v___x_2243_);
v___x_2245_ = v___x_2227_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_namePrefix_2224_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
lean_object* v___x_2247_; 
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 2, v___x_2245_);
v___x_2247_ = v___x_2239_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_env_2230_);
lean_ctor_set(v_reuseFailAlloc_2250_, 1, v_nextMacroScope_2231_);
lean_ctor_set(v_reuseFailAlloc_2250_, 2, v___x_2245_);
lean_ctor_set(v_reuseFailAlloc_2250_, 3, v_auxDeclNGen_2232_);
lean_ctor_set(v_reuseFailAlloc_2250_, 4, v_traceState_2233_);
lean_ctor_set(v_reuseFailAlloc_2250_, 5, v_cache_2234_);
lean_ctor_set(v_reuseFailAlloc_2250_, 6, v_messages_2235_);
lean_ctor_set(v_reuseFailAlloc_2250_, 7, v_infoState_2236_);
lean_ctor_set(v_reuseFailAlloc_2250_, 8, v_snapshotTasks_2237_);
v___x_2247_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = lean_st_ref_put(v___y_2220_, v___x_2247_);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v_r_2241_);
return v___x_2249_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg___boxed(lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg(v___y_2255_);
lean_dec(v___y_2255_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0(lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___x_2267_; lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
v___x_2267_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg(v___y_2265_);
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2267_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2267_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0___boxed(lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0(v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(lean_object* v_n_2288_, lean_object* v_type_2289_, lean_object* v_value_x3f_2290_, uint8_t v_tainted_2291_, uint8_t v_isCandidate_2292_, lean_object* v_k_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0(v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2305_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc_n(v_a_2304_, 2);
lean_dec_ref_known(v___x_2303_, 1);
v___x_2305_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(v_a_2304_, v_a_2297_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v_lctx_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___f_2310_; lean_object* v___y_2312_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v_lctx_2307_ = lean_ctor_get(v_a_2298_, 2);
v___x_2308_ = lean_box(v_tainted_2291_);
v___x_2309_ = lean_box(v_isCandidate_2292_);
v___f_2310_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2310_, 0, v_k_2293_);
lean_closure_set(v___f_2310_, 1, v_a_2306_);
lean_closure_set(v___f_2310_, 2, v___x_2308_);
lean_closure_set(v___f_2310_, 3, v___x_2309_);
if (lean_obj_tag(v_value_x3f_2290_) == 0)
{
uint8_t v___x_2315_; uint8_t v___x_2316_; lean_object* v___x_2317_; 
v___x_2315_ = 0;
v___x_2316_ = 0;
lean_inc_ref(v_lctx_2307_);
v___x_2317_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2307_, v_a_2304_, v_n_2288_, v_type_2289_, v___x_2315_, v___x_2316_);
v___y_2312_ = v___x_2317_;
goto v___jp_2311_;
}
else
{
lean_object* v_val_2318_; lean_object* v_fst_2319_; lean_object* v_snd_2320_; uint8_t v___x_2321_; uint8_t v___x_2322_; lean_object* v___x_2323_; 
v_val_2318_ = lean_ctor_get(v_value_x3f_2290_, 0);
lean_inc(v_val_2318_);
lean_dec_ref_known(v_value_x3f_2290_, 1);
v_fst_2319_ = lean_ctor_get(v_val_2318_, 0);
lean_inc(v_fst_2319_);
v_snd_2320_ = lean_ctor_get(v_val_2318_, 1);
lean_inc(v_snd_2320_);
lean_dec(v_val_2318_);
v___x_2321_ = 0;
v___x_2322_ = lean_unbox(v_snd_2320_);
lean_dec(v_snd_2320_);
lean_inc_ref(v_lctx_2307_);
v___x_2323_ = l_Lean_LocalContext_mkLetDecl(v_lctx_2307_, v_a_2304_, v_n_2288_, v_type_2289_, v_fst_2319_, v___x_2322_, v___x_2321_);
v___y_2312_ = v___x_2323_;
goto v___jp_2311_;
}
v___jp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___closed__0));
v___x_2314_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(v___y_2312_, v___x_2313_, v___f_2310_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
return v___x_2314_;
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec(v_a_2304_);
lean_dec_ref(v_k_2293_);
lean_dec(v_value_x3f_2290_);
lean_dec_ref(v_type_2289_);
lean_dec(v_n_2288_);
v_a_2324_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2305_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2305_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec_ref(v_k_2293_);
lean_dec(v_value_x3f_2290_);
lean_dec_ref(v_type_2289_);
lean_dec(v_n_2288_);
v_a_2332_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2303_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2303_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___boxed(lean_object* v_n_2340_, lean_object* v_type_2341_, lean_object* v_value_x3f_2342_, lean_object* v_tainted_2343_, lean_object* v_isCandidate_2344_, lean_object* v_k_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
uint8_t v_tainted_boxed_2355_; uint8_t v_isCandidate_boxed_2356_; lean_object* v_res_2357_; 
v_tainted_boxed_2355_ = lean_unbox(v_tainted_2343_);
v_isCandidate_boxed_2356_ = lean_unbox(v_isCandidate_2344_);
v_res_2357_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_n_2340_, v_type_2341_, v_value_x3f_2342_, v_tainted_boxed_2355_, v_isCandidate_boxed_2356_, v_k_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder(lean_object* v_00_u03b1_2358_, lean_object* v_n_2359_, lean_object* v_type_2360_, lean_object* v_value_x3f_2361_, uint8_t v_tainted_2362_, uint8_t v_isCandidate_2363_, lean_object* v_k_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_n_2359_, v_type_2360_, v_value_x3f_2361_, v_tainted_2362_, v_isCandidate_2363_, v_k_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___boxed(lean_object* v_00_u03b1_2375_, lean_object* v_n_2376_, lean_object* v_type_2377_, lean_object* v_value_x3f_2378_, lean_object* v_tainted_2379_, lean_object* v_isCandidate_2380_, lean_object* v_k_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
uint8_t v_tainted_boxed_2391_; uint8_t v_isCandidate_boxed_2392_; lean_object* v_res_2393_; 
v_tainted_boxed_2391_ = lean_unbox(v_tainted_2379_);
v_isCandidate_boxed_2392_ = lean_unbox(v_isCandidate_2380_);
v_res_2393_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder(v_00_u03b1_2375_, v_n_2376_, v_type_2377_, v_value_x3f_2378_, v_tainted_boxed_2391_, v_isCandidate_boxed_2392_, v_k_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0(lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg(v___y_2401_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___boxed(lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0(v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0(lean_object* v_msg_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v_toApplicative_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2491_; 
v___x_2424_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0);
v___x_2425_ = l_StateRefT_x27_instMonad___redArg(v___x_2424_);
v_toApplicative_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2491_ == 0)
{
lean_object* v_unused_2492_; 
v_unused_2492_ = lean_ctor_get(v___x_2425_, 1);
lean_dec(v_unused_2492_);
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2491_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_toApplicative_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2491_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v_toFunctor_2430_; lean_object* v_toSeq_2431_; lean_object* v_toSeqLeft_2432_; lean_object* v_toSeqRight_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2489_; 
v_toFunctor_2430_ = lean_ctor_get(v_toApplicative_2426_, 0);
v_toSeq_2431_ = lean_ctor_get(v_toApplicative_2426_, 2);
v_toSeqLeft_2432_ = lean_ctor_get(v_toApplicative_2426_, 3);
v_toSeqRight_2433_ = lean_ctor_get(v_toApplicative_2426_, 4);
v_isSharedCheck_2489_ = !lean_is_exclusive(v_toApplicative_2426_);
if (v_isSharedCheck_2489_ == 0)
{
lean_object* v_unused_2490_; 
v_unused_2490_ = lean_ctor_get(v_toApplicative_2426_, 1);
lean_dec(v_unused_2490_);
v___x_2435_ = v_toApplicative_2426_;
v_isShared_2436_ = v_isSharedCheck_2489_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_toSeqRight_2433_);
lean_inc(v_toSeqLeft_2432_);
lean_inc(v_toSeq_2431_);
lean_inc(v_toFunctor_2430_);
lean_dec(v_toApplicative_2426_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2489_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___f_2437_; lean_object* v___f_2438_; lean_object* v___f_2439_; lean_object* v___f_2440_; lean_object* v___x_2441_; lean_object* v___f_2442_; lean_object* v___f_2443_; lean_object* v___f_2444_; lean_object* v___x_2446_; 
v___f_2437_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__1));
v___f_2438_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__2));
lean_inc_ref(v_toFunctor_2430_);
v___f_2439_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2439_, 0, v_toFunctor_2430_);
v___f_2440_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2440_, 0, v_toFunctor_2430_);
v___x_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___f_2439_);
lean_ctor_set(v___x_2441_, 1, v___f_2440_);
v___f_2442_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2442_, 0, v_toSeqRight_2433_);
v___f_2443_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2443_, 0, v_toSeqLeft_2432_);
v___f_2444_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2444_, 0, v_toSeq_2431_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 4, v___f_2442_);
lean_ctor_set(v___x_2435_, 3, v___f_2443_);
lean_ctor_set(v___x_2435_, 2, v___f_2444_);
lean_ctor_set(v___x_2435_, 1, v___f_2437_);
lean_ctor_set(v___x_2435_, 0, v___x_2441_);
v___x_2446_ = v___x_2435_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2441_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v___f_2437_);
lean_ctor_set(v_reuseFailAlloc_2488_, 2, v___f_2444_);
lean_ctor_set(v_reuseFailAlloc_2488_, 3, v___f_2443_);
lean_ctor_set(v_reuseFailAlloc_2488_, 4, v___f_2442_);
v___x_2446_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2448_; 
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 1, v___f_2438_);
lean_ctor_set(v___x_2428_, 0, v___x_2446_);
v___x_2448_ = v___x_2428_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v___f_2438_);
v___x_2448_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2449_; lean_object* v_toApplicative_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2485_; 
v___x_2449_ = l_StateRefT_x27_instMonad___redArg(v___x_2448_);
v_toApplicative_2450_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2485_ == 0)
{
lean_object* v_unused_2486_; 
v_unused_2486_ = lean_ctor_get(v___x_2449_, 1);
lean_dec(v_unused_2486_);
v___x_2452_ = v___x_2449_;
v_isShared_2453_ = v_isSharedCheck_2485_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_toApplicative_2450_);
lean_dec(v___x_2449_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2485_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v_toFunctor_2454_; lean_object* v_toSeq_2455_; lean_object* v_toSeqLeft_2456_; lean_object* v_toSeqRight_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2483_; 
v_toFunctor_2454_ = lean_ctor_get(v_toApplicative_2450_, 0);
v_toSeq_2455_ = lean_ctor_get(v_toApplicative_2450_, 2);
v_toSeqLeft_2456_ = lean_ctor_get(v_toApplicative_2450_, 3);
v_toSeqRight_2457_ = lean_ctor_get(v_toApplicative_2450_, 4);
v_isSharedCheck_2483_ = !lean_is_exclusive(v_toApplicative_2450_);
if (v_isSharedCheck_2483_ == 0)
{
lean_object* v_unused_2484_; 
v_unused_2484_ = lean_ctor_get(v_toApplicative_2450_, 1);
lean_dec(v_unused_2484_);
v___x_2459_ = v_toApplicative_2450_;
v_isShared_2460_ = v_isSharedCheck_2483_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_toSeqRight_2457_);
lean_inc(v_toSeqLeft_2456_);
lean_inc(v_toSeq_2455_);
lean_inc(v_toFunctor_2454_);
lean_dec(v_toApplicative_2450_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2483_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___f_2461_; lean_object* v___f_2462_; lean_object* v___f_2463_; lean_object* v___f_2464_; lean_object* v___x_2465_; lean_object* v___f_2466_; lean_object* v___f_2467_; lean_object* v___f_2468_; lean_object* v___x_2470_; 
v___f_2461_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__3));
v___f_2462_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__4));
lean_inc_ref(v_toFunctor_2454_);
v___f_2463_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2463_, 0, v_toFunctor_2454_);
v___f_2464_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2464_, 0, v_toFunctor_2454_);
v___x_2465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___f_2463_);
lean_ctor_set(v___x_2465_, 1, v___f_2464_);
v___f_2466_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2466_, 0, v_toSeqRight_2457_);
v___f_2467_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2467_, 0, v_toSeqLeft_2456_);
v___f_2468_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2468_, 0, v_toSeq_2455_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 4, v___f_2466_);
lean_ctor_set(v___x_2459_, 3, v___f_2467_);
lean_ctor_set(v___x_2459_, 2, v___f_2468_);
lean_ctor_set(v___x_2459_, 1, v___f_2461_);
lean_ctor_set(v___x_2459_, 0, v___x_2465_);
v___x_2470_ = v___x_2459_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2465_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v___f_2461_);
lean_ctor_set(v_reuseFailAlloc_2482_, 2, v___f_2468_);
lean_ctor_set(v_reuseFailAlloc_2482_, 3, v___f_2467_);
lean_ctor_set(v_reuseFailAlloc_2482_, 4, v___f_2466_);
v___x_2470_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
lean_object* v___x_2472_; 
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 1, v___f_2462_);
lean_ctor_set(v___x_2452_, 0, v___x_2470_);
v___x_2472_ = v___x_2452_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2470_);
lean_ctor_set(v_reuseFailAlloc_2481_, 1, v___f_2462_);
v___x_2472_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___f_2478_; lean_object* v___x_5629__overap_2479_; lean_object* v___x_2480_; 
v___x_2473_ = l_StateRefT_x27_instMonad___redArg(v___x_2472_);
v___x_2474_ = l_ReaderT_instMonad___redArg(v___x_2473_);
v___x_2475_ = l_StateRefT_x27_instMonad___redArg(v___x_2474_);
v___x_2476_ = lean_box(0);
v___x_2477_ = l_instInhabitedOfMonad___redArg(v___x_2475_, v___x_2476_);
v___f_2478_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2478_, 0, v___x_2477_);
v___x_5629__overap_2479_ = lean_panic_fn_borrowed(v___f_2478_, v_msg_2414_);
lean_dec_ref(v___f_2478_);
lean_inc(v___y_2422_);
lean_inc_ref(v___y_2421_);
lean_inc(v___y_2420_);
lean_inc_ref(v___y_2419_);
lean_inc(v___y_2418_);
lean_inc_ref(v___y_2417_);
lean_inc(v___y_2416_);
lean_inc_ref(v___y_2415_);
v___x_2480_ = lean_apply_9(v___x_5629__overap_2479_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, lean_box(0));
return v___x_2480_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0___boxed(lean_object* v_msg_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0(v_msg_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0___boxed(lean_object* v_body_2504_, lean_object* v_body_2505_, lean_object* v_x_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0(v_body_2504_, v_body_2505_, v_x_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec_ref(v_x_2506_);
return v_res_2516_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__1(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2518_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_2519_ = lean_unsigned_to_nat(42u);
v___x_2520_ = lean_unsigned_to_nat(340u);
v___x_2521_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__0));
v___x_2522_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0));
v___x_2523_ = l_mkPanicMessageWithDecl(v___x_2522_, v___x_2521_, v___x_2520_, v___x_2519_, v___x_2518_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(lean_object* v_e_2524_, lean_object* v_expected_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_){
_start:
{
if (lean_obj_tag(v_e_2524_) == 6)
{
lean_object* v_binderName_2535_; lean_object* v_binderType_2536_; lean_object* v_body_2537_; lean_object* v___x_2538_; 
v_binderName_2535_ = lean_ctor_get(v_e_2524_, 0);
lean_inc(v_binderName_2535_);
v_binderType_2536_ = lean_ctor_get(v_e_2524_, 1);
lean_inc_ref(v_binderType_2536_);
v_body_2537_ = lean_ctor_get(v_e_2524_, 2);
lean_inc_ref(v_body_2537_);
lean_dec_ref_known(v_e_2524_, 3);
v___x_2538_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_expected_2525_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref_known(v___x_2538_, 1);
if (lean_obj_tag(v_a_2539_) == 7)
{
lean_object* v_binderType_2540_; lean_object* v_body_2541_; lean_object* v___x_2542_; 
v_binderType_2540_ = lean_ctor_get(v_a_2539_, 1);
lean_inc_ref(v_binderType_2540_);
v_body_2541_ = lean_ctor_get(v_a_2539_, 2);
lean_inc_ref(v_body_2541_);
lean_dec_ref_known(v_a_2539_, 3);
lean_inc_ref(v_binderType_2536_);
v___x_2542_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_binderType_2536_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2544_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc_n(v_a_2543_, 2);
lean_dec_ref_known(v___x_2542_, 1);
v___x_2544_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_a_2543_, v_binderType_2540_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_cleanSuffix_2545_; lean_object* v___f_2546_; lean_object* v___x_2547_; uint8_t v___y_2549_; lean_object* v___x_2552_; uint8_t v___x_2553_; 
lean_dec_ref_known(v___x_2544_, 1);
v_cleanSuffix_2545_ = lean_ctor_get(v_a_2526_, 2);
v___f_2546_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0___boxed), 12, 2);
lean_closure_set(v___f_2546_, 0, v_body_2541_);
lean_closure_set(v___f_2546_, 1, v_body_2537_);
v___x_2547_ = lean_box(0);
v___x_2552_ = l_Lean_Expr_looseBVarRange(v_binderType_2536_);
lean_dec_ref(v_binderType_2536_);
v___x_2553_ = lean_nat_dec_le(v___x_2552_, v_cleanSuffix_2545_);
lean_dec(v___x_2552_);
if (v___x_2553_ == 0)
{
uint8_t v___x_2554_; 
v___x_2554_ = 1;
v___y_2549_ = v___x_2554_;
goto v___jp_2548_;
}
else
{
uint8_t v___x_2555_; 
v___x_2555_ = 0;
v___y_2549_ = v___x_2555_;
goto v___jp_2548_;
}
v___jp_2548_:
{
uint8_t v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = 0;
v___x_2551_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_binderName_2535_, v_a_2543_, v___x_2547_, v___y_2549_, v___x_2550_, v___f_2546_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
return v___x_2551_;
}
}
else
{
lean_dec(v_a_2543_);
lean_dec_ref(v_body_2541_);
lean_dec_ref(v_body_2537_);
lean_dec_ref(v_binderType_2536_);
lean_dec(v_binderName_2535_);
return v___x_2544_;
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec_ref(v_body_2541_);
lean_dec_ref(v_binderType_2540_);
lean_dec_ref(v_body_2537_);
lean_dec_ref(v_binderType_2536_);
lean_dec(v_binderName_2535_);
v_a_2556_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2542_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2542_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
else
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
lean_dec(v_a_2539_);
lean_dec_ref(v_body_2537_);
lean_dec_ref(v_binderType_2536_);
lean_dec(v_binderName_2535_);
v___x_2564_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__1);
v___x_2565_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0(v___x_2564_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
return v___x_2565_;
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec_ref(v_body_2537_);
lean_dec_ref(v_binderType_2536_);
lean_dec(v_binderName_2535_);
v_a_2566_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2538_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2538_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
else
{
lean_object* v___x_2574_; 
v___x_2574_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_e_2524_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2576_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_a_2575_);
lean_dec_ref_known(v___x_2574_, 1);
v___x_2576_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_a_2575_, v_expected_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
return v___x_2576_;
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_dec_ref(v_expected_2525_);
v_a_2577_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2574_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2574_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0(lean_object* v_body_2585_, lean_object* v_body_2586_, lean_object* v_x_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
uint8_t v___x_2597_; 
v___x_2597_ = l_Lean_Expr_hasLooseBVars(v_body_2585_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; 
v___x_2598_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_body_2586_, v_body_2585_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
return v___x_2598_;
}
else
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2599_ = lean_expr_instantiate1(v_body_2585_, v_x_2587_);
lean_dec_ref(v_body_2585_);
v___x_2600_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2599_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v___x_2602_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref_known(v___x_2600_, 1);
v___x_2602_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_body_2586_, v_a_2601_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
return v___x_2602_;
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_dec_ref(v_body_2586_);
v_a_2603_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2600_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2600_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___boxed(lean_object* v_e_2611_, lean_object* v_expected_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_e_2611_, v_expected_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
lean_dec(v_a_2618_);
lean_dec_ref(v_a_2617_);
lean_dec(v_a_2616_);
lean_dec_ref(v_a_2615_);
lean_dec(v_a_2614_);
lean_dec_ref(v_a_2613_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(lean_object* v_t_2623_, lean_object* v_tf_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_){
_start:
{
lean_object* v_numCandidates_2634_; lean_object* v_cleanSuffix_2635_; lean_object* v___x_2636_; uint8_t v___x_2637_; 
v_numCandidates_2634_ = lean_ctor_get(v_a_2625_, 1);
v_cleanSuffix_2635_ = lean_ctor_get(v_a_2625_, 2);
v___x_2636_ = lean_unsigned_to_nat(0u);
v___x_2637_ = lean_nat_dec_lt(v___x_2636_, v_numCandidates_2634_);
if (v___x_2637_ == 0)
{
lean_dec_ref(v_tf_2624_);
goto v___jp_2631_;
}
else
{
lean_object* v___x_2638_; uint8_t v___x_2639_; 
v___x_2638_ = l_Lean_Expr_looseBVarRange(v_t_2623_);
v___x_2639_ = lean_nat_dec_le(v___x_2638_, v_cleanSuffix_2635_);
lean_dec(v___x_2638_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; 
v___x_2640_ = l_Lean_Meta_getLevel(v_tf_2624_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2648_; 
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2648_ == 0)
{
lean_object* v_unused_2649_; 
v_unused_2649_ = lean_ctor_get(v___x_2640_, 0);
lean_dec(v_unused_2649_);
v___x_2642_ = v___x_2640_;
v_isShared_2643_ = v_isSharedCheck_2648_;
goto v_resetjp_2641_;
}
else
{
lean_dec(v___x_2640_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2648_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2644_; lean_object* v___x_2646_; 
v___x_2644_ = lean_box(0);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v___x_2644_);
v___x_2646_ = v___x_2642_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
v_a_2650_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2640_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2640_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
else
{
lean_dec_ref(v_tf_2624_);
goto v___jp_2631_;
}
}
v___jp_2631_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2632_ = lean_box(0);
v___x_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
return v___x_2633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg___boxed(lean_object* v_t_2658_, lean_object* v_tf_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_t_2658_, v_tf_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec_ref(v_t_2658_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain(lean_object* v_t_2667_, lean_object* v_tf_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_t_2667_, v_tf_2668_, v_a_2669_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___boxed(lean_object* v_t_2679_, lean_object* v_tf_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain(v_t_2679_, v_tf_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec_ref(v_t_2679_);
return v_res_2690_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1(void){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2692_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_2693_ = lean_unsigned_to_nat(35u);
v___x_2694_ = lean_unsigned_to_nat(322u);
v___x_2695_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__0));
v___x_2696_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0));
v___x_2697_ = l_mkPanicMessageWithDecl(v___x_2696_, v___x_2695_, v___x_2694_, v___x_2693_, v___x_2692_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp(lean_object* v_f_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_f_2698_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2711_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref_known(v___x_2709_, 1);
v___x_2711_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_a_2710_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2739_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2714_ = v___x_2711_;
v_isShared_2715_ = v_isSharedCheck_2739_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2711_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2739_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
if (lean_obj_tag(v_a_2712_) == 7)
{
lean_object* v_binderType_2716_; uint8_t v___x_2731_; 
v_binderType_2716_ = lean_ctor_get(v_a_2712_, 1);
lean_inc_ref(v_binderType_2716_);
lean_dec_ref_known(v_a_2712_, 3);
v___x_2731_ = l_Lean_Expr_hasLooseBVars(v_a_2699_);
if (v___x_2731_ == 0)
{
uint8_t v___x_2732_; 
v___x_2732_ = l_Lean_Expr_hasFVar(v_binderType_2716_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; lean_object* v___x_2735_; 
lean_dec_ref(v_binderType_2716_);
lean_dec_ref(v_a_2699_);
v___x_2733_ = lean_box(0);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 0, v___x_2733_);
v___x_2735_ = v___x_2714_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
else
{
lean_del_object(v___x_2714_);
goto v___jp_2717_;
}
}
else
{
lean_del_object(v___x_2714_);
goto v___jp_2717_;
}
v___jp_2717_:
{
uint8_t v___x_2718_; 
v___x_2718_ = l_Lean_Expr_isLambda(v_a_2699_);
if (v___x_2718_ == 0)
{
lean_object* v___x_2719_; 
v___x_2719_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; lean_object* v___x_2721_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref_known(v___x_2719_, 1);
v___x_2721_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_a_2720_, v_binderType_2716_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
return v___x_2721_;
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec_ref(v_binderType_2716_);
v_a_2722_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2719_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2719_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
else
{
lean_object* v___x_2730_; 
v___x_2730_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_a_2699_, v_binderType_2716_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
return v___x_2730_;
}
}
}
else
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
lean_del_object(v___x_2714_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2699_);
v___x_2737_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1);
v___x_2738_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0(v___x_2737_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
return v___x_2738_;
}
}
}
else
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
lean_dec_ref(v_a_2699_);
v_a_2740_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2711_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2711_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
lean_dec_ref(v_a_2699_);
v_a_2748_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2709_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2709_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___boxed(lean_object* v_f_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp(v_f_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_);
lean_dec(v_a_2765_);
lean_dec_ref(v_a_2764_);
lean_dec(v_a_2763_);
lean_dec_ref(v_a_2762_);
lean_dec(v_a_2761_);
lean_dec_ref(v_a_2760_);
lean_dec(v_a_2759_);
lean_dec_ref(v_a_2758_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(lean_object* v_x_2768_, uint8_t v_bi_2769_, lean_object* v_t_2770_, lean_object* v_b_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v___y_2780_; lean_object* v___x_2783_; uint8_t v_debug_2784_; 
v___x_2783_ = lean_st_ref_get(v___y_2773_);
v_debug_2784_ = lean_ctor_get_uint8(v___x_2783_, sizeof(void*)*11);
lean_dec(v___x_2783_);
if (v_debug_2784_ == 0)
{
v___y_2780_ = v___y_2773_;
goto v___jp_2779_;
}
else
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2770_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v___x_2786_; 
lean_dec_ref_known(v___x_2785_, 1);
v___x_2786_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_dec_ref_known(v___x_2786_, 1);
v___y_2780_ = v___y_2773_;
goto v___jp_2779_;
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
lean_dec_ref(v_b_2771_);
lean_dec_ref(v_t_2770_);
lean_dec(v_x_2768_);
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2786_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2786_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_dec_ref(v_b_2771_);
lean_dec_ref(v_t_2770_);
lean_dec(v_x_2768_);
v_a_2795_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2785_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2785_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
v___jp_2779_:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = l_Lean_Expr_lam___override(v_x_2768_, v_t_2770_, v_b_2771_, v_bi_2769_);
v___x_2782_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2781_, v___y_2780_);
return v___x_2782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg___boxed(lean_object* v_x_2803_, lean_object* v_bi_2804_, lean_object* v_t_2805_, lean_object* v_b_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
uint8_t v_bi_boxed_2814_; lean_object* v_res_2815_; 
v_bi_boxed_2814_ = lean_unbox(v_bi_2804_);
v_res_2815_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(v_x_2803_, v_bi_boxed_2814_, v_t_2805_, v_b_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(lean_object* v_x_2816_, lean_object* v_t_2817_, lean_object* v_v_2818_, lean_object* v_b_2819_, uint8_t v_nondep_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v___y_2829_; lean_object* v___x_2832_; uint8_t v_debug_2833_; 
v___x_2832_ = lean_st_ref_get(v___y_2822_);
v_debug_2833_ = lean_ctor_get_uint8(v___x_2832_, sizeof(void*)*11);
lean_dec(v___x_2832_);
if (v_debug_2833_ == 0)
{
v___y_2829_ = v___y_2822_;
goto v___jp_2828_;
}
else
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2817_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v___x_2835_; 
lean_dec_ref_known(v___x_2834_, 1);
v___x_2835_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_v_2818_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v___x_2836_; 
lean_dec_ref_known(v___x_2835_, 1);
v___x_2836_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2819_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_dec_ref_known(v___x_2836_, 1);
v___y_2829_ = v___y_2822_;
goto v___jp_2828_;
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_dec_ref(v_b_2819_);
lean_dec_ref(v_v_2818_);
lean_dec_ref(v_t_2817_);
lean_dec(v_x_2816_);
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2836_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2836_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_dec_ref(v_b_2819_);
lean_dec_ref(v_v_2818_);
lean_dec_ref(v_t_2817_);
lean_dec(v_x_2816_);
v_a_2845_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2835_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2835_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
else
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
lean_dec_ref(v_b_2819_);
lean_dec_ref(v_v_2818_);
lean_dec_ref(v_t_2817_);
lean_dec(v_x_2816_);
v_a_2853_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2834_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2834_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
v___jp_2828_:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = l_Lean_Expr_letE___override(v_x_2816_, v_t_2817_, v_v_2818_, v_b_2819_, v_nondep_2820_);
v___x_2831_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2830_, v___y_2829_);
return v___x_2831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg___boxed(lean_object* v_x_2861_, lean_object* v_t_2862_, lean_object* v_v_2863_, lean_object* v_b_2864_, lean_object* v_nondep_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
uint8_t v_nondep_boxed_2873_; lean_object* v_res_2874_; 
v_nondep_boxed_2873_ = lean_unbox(v_nondep_2865_);
v_res_2874_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_x_2861_, v_t_2862_, v_v_2863_, v_b_2864_, v_nondep_boxed_2873_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
return v_res_2874_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(lean_object* v_k_2875_, lean_object* v_t_2876_){
_start:
{
if (lean_obj_tag(v_t_2876_) == 0)
{
lean_object* v_k_2877_; lean_object* v_l_2878_; lean_object* v_r_2879_; uint8_t v___x_2880_; 
v_k_2877_ = lean_ctor_get(v_t_2876_, 1);
v_l_2878_ = lean_ctor_get(v_t_2876_, 3);
v_r_2879_ = lean_ctor_get(v_t_2876_, 4);
v___x_2880_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2875_, v_k_2877_);
switch(v___x_2880_)
{
case 0:
{
v_t_2876_ = v_l_2878_;
goto _start;
}
case 1:
{
uint8_t v___x_2882_; 
v___x_2882_ = 1;
return v___x_2882_;
}
default: 
{
v_t_2876_ = v_r_2879_;
goto _start;
}
}
}
else
{
uint8_t v___x_2884_; 
v___x_2884_ = 0;
return v___x_2884_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg___boxed(lean_object* v_k_2885_, lean_object* v_t_2886_){
_start:
{
uint8_t v_res_2887_; lean_object* v_r_2888_; 
v_res_2887_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(v_k_2885_, v_t_2886_);
lean_dec(v_t_2886_);
lean_dec(v_k_2885_);
v_r_2888_ = lean_box(v_res_2887_);
return v_r_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(lean_object* v_x_2889_, uint8_t v_bi_2890_, lean_object* v_t_2891_, lean_object* v_b_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v___y_2901_; lean_object* v___x_2904_; uint8_t v_debug_2905_; 
v___x_2904_ = lean_st_ref_get(v___y_2894_);
v_debug_2905_ = lean_ctor_get_uint8(v___x_2904_, sizeof(void*)*11);
lean_dec(v___x_2904_);
if (v_debug_2905_ == 0)
{
v___y_2901_ = v___y_2894_;
goto v___jp_2900_;
}
else
{
lean_object* v___x_2906_; 
v___x_2906_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2891_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v___x_2907_; 
lean_dec_ref_known(v___x_2906_, 1);
v___x_2907_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_dec_ref_known(v___x_2907_, 1);
v___y_2901_ = v___y_2894_;
goto v___jp_2900_;
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec_ref(v_b_2892_);
lean_dec_ref(v_t_2891_);
lean_dec(v_x_2889_);
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2907_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2907_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec_ref(v_b_2892_);
lean_dec_ref(v_t_2891_);
lean_dec(v_x_2889_);
v_a_2916_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2906_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2906_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
v___jp_2900_:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = l_Lean_Expr_forallE___override(v_x_2889_, v_t_2891_, v_b_2892_, v_bi_2890_);
v___x_2903_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2902_, v___y_2901_);
return v___x_2903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg___boxed(lean_object* v_x_2924_, lean_object* v_bi_2925_, lean_object* v_t_2926_, lean_object* v_b_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
uint8_t v_bi_boxed_2935_; lean_object* v_res_2936_; 
v_bi_boxed_2935_ = lean_unbox(v_bi_2925_);
v_res_2936_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(v_x_2924_, v_bi_boxed_2935_, v_t_2926_, v_b_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(lean_object* v_d_2937_, lean_object* v_e_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v___y_2947_; lean_object* v___x_2950_; uint8_t v_debug_2951_; 
v___x_2950_ = lean_st_ref_get(v___y_2940_);
v_debug_2951_ = lean_ctor_get_uint8(v___x_2950_, sizeof(void*)*11);
lean_dec(v___x_2950_);
if (v_debug_2951_ == 0)
{
v___y_2947_ = v___y_2940_;
goto v___jp_2946_;
}
else
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_dec_ref_known(v___x_2952_, 1);
v___y_2947_ = v___y_2940_;
goto v___jp_2946_;
}
else
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
lean_dec_ref(v_e_2938_);
lean_dec(v_d_2937_);
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2952_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
v___jp_2946_:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2948_ = l_Lean_Expr_mdata___override(v_d_2937_, v_e_2938_);
v___x_2949_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2948_, v___y_2947_);
return v___x_2949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg___boxed(lean_object* v_d_2961_, lean_object* v_e_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(v_d_2961_, v_e_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(lean_object* v_structName_2971_, lean_object* v_idx_2972_, lean_object* v_struct_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v___y_2982_; lean_object* v___x_2985_; uint8_t v_debug_2986_; 
v___x_2985_ = lean_st_ref_get(v___y_2975_);
v_debug_2986_ = lean_ctor_get_uint8(v___x_2985_, sizeof(void*)*11);
lean_dec(v___x_2985_);
if (v_debug_2986_ == 0)
{
v___y_2982_ = v___y_2975_;
goto v___jp_2981_;
}
else
{
lean_object* v___x_2987_; 
v___x_2987_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_struct_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_dec_ref_known(v___x_2987_, 1);
v___y_2982_ = v___y_2975_;
goto v___jp_2981_;
}
else
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2995_; 
lean_dec_ref(v_struct_2973_);
lean_dec(v_idx_2972_);
lean_dec(v_structName_2971_);
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2990_ = v___x_2987_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2987_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
v___jp_2981_:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = l_Lean_Expr_proj___override(v_structName_2971_, v_idx_2972_, v_struct_2973_);
v___x_2984_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2983_, v___y_2982_);
return v___x_2984_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg___boxed(lean_object* v_structName_2996_, lean_object* v_idx_2997_, lean_object* v_struct_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(v_structName_2996_, v_idx_2997_, v_struct_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(lean_object* v_f_3007_, lean_object* v_a_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
lean_object* v___y_3017_; lean_object* v___x_3020_; uint8_t v_debug_3021_; 
v___x_3020_ = lean_st_ref_get(v___y_3010_);
v_debug_3021_ = lean_ctor_get_uint8(v___x_3020_, sizeof(void*)*11);
lean_dec(v___x_3020_);
if (v_debug_3021_ == 0)
{
v___y_3017_ = v___y_3010_;
goto v___jp_3016_;
}
else
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_3007_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v___x_3023_; 
lean_dec_ref_known(v___x_3022_, 1);
v___x_3023_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_dec_ref_known(v___x_3023_, 1);
v___y_3017_ = v___y_3010_;
goto v___jp_3016_;
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
lean_dec_ref(v_a_3008_);
lean_dec_ref(v_f_3007_);
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_3023_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3023_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec_ref(v_a_3008_);
lean_dec_ref(v_f_3007_);
v_a_3032_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3022_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3022_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
v___jp_3016_:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = l_Lean_Expr_app___override(v_f_3007_, v_a_3008_);
v___x_3019_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_3018_, v___y_3017_);
return v___x_3019_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg___boxed(lean_object* v_f_3040_, lean_object* v_a_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(v_f_3040_, v_a_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(lean_object* v_a_3050_, lean_object* v_visited_3051_, lean_object* v_types_3052_, lean_object* v_subst_3053_, lean_object* v_a_x3f_3054_){
_start:
{
lean_object* v___x_3056_; lean_object* v_visitedClosed_3057_; lean_object* v_hasDepLetCache_3058_; lean_object* v_numConverted_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3069_; 
v___x_3056_ = lean_st_ref_take(v_a_3050_);
v_visitedClosed_3057_ = lean_ctor_get(v___x_3056_, 3);
v_hasDepLetCache_3058_ = lean_ctor_get(v___x_3056_, 4);
v_numConverted_3059_ = lean_ctor_get(v___x_3056_, 5);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3069_ == 0)
{
lean_object* v_unused_3070_; lean_object* v_unused_3071_; lean_object* v_unused_3072_; 
v_unused_3070_ = lean_ctor_get(v___x_3056_, 2);
lean_dec(v_unused_3070_);
v_unused_3071_ = lean_ctor_get(v___x_3056_, 1);
lean_dec(v_unused_3071_);
v_unused_3072_ = lean_ctor_get(v___x_3056_, 0);
lean_dec(v_unused_3072_);
v___x_3061_ = v___x_3056_;
v_isShared_3062_ = v_isSharedCheck_3069_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_numConverted_3059_);
lean_inc(v_hasDepLetCache_3058_);
lean_inc(v_visitedClosed_3057_);
lean_dec(v___x_3056_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3069_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 2, v_subst_3053_);
lean_ctor_set(v___x_3061_, 1, v_types_3052_);
lean_ctor_set(v___x_3061_, 0, v_visited_3051_);
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_visited_3051_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v_types_3052_);
lean_ctor_set(v_reuseFailAlloc_3068_, 2, v_subst_3053_);
lean_ctor_set(v_reuseFailAlloc_3068_, 3, v_visitedClosed_3057_);
lean_ctor_set(v_reuseFailAlloc_3068_, 4, v_hasDepLetCache_3058_);
lean_ctor_set(v_reuseFailAlloc_3068_, 5, v_numConverted_3059_);
v___x_3064_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = lean_st_ref_put(v_a_3050_, v___x_3064_);
v___x_3066_ = lean_box(0);
v___x_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
return v___x_3067_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0___boxed(lean_object* v_a_3073_, lean_object* v_visited_3074_, lean_object* v_types_3075_, lean_object* v_subst_3076_, lean_object* v_a_x3f_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(v_a_3073_, v_visited_3074_, v_types_3075_, v_subst_3076_, v_a_x3f_3077_);
lean_dec(v_a_x3f_3077_);
lean_dec(v_a_3073_);
return v_res_3079_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = lean_unsigned_to_nat(32u);
v___x_3081_ = lean_mk_empty_array_with_capacity(v___x_3080_);
v___x_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
return v___x_3082_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1(void){
_start:
{
size_t v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3083_ = ((size_t)5ULL);
v___x_3084_ = lean_unsigned_to_nat(0u);
v___x_3085_ = lean_unsigned_to_nat(32u);
v___x_3086_ = lean_mk_empty_array_with_capacity(v___x_3085_);
v___x_3087_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0);
v___x_3088_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
lean_ctor_set(v___x_3088_, 1, v___x_3086_);
lean_ctor_set(v___x_3088_, 2, v___x_3084_);
lean_ctor_set(v___x_3088_, 3, v___x_3084_);
lean_ctor_set_usize(v___x_3088_, 4, v___x_3083_);
return v___x_3088_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2(void){
_start:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3089_ = lean_unsigned_to_nat(0u);
v___x_3090_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1);
v___x_3091_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
lean_ctor_set(v___x_3091_, 1, v___x_3089_);
lean_ctor_set(v___x_3091_, 2, v___x_3089_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0___boxed(lean_object* v_body_3092_, lean_object* v_binderType_3093_, lean_object* v_a_3094_, lean_object* v_binderName_3095_, lean_object* v_binderInfo_3096_, lean_object* v_e_3097_, lean_object* v_x_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
uint8_t v_binderInfo_76003__boxed_3108_; lean_object* v_res_3109_; 
v_binderInfo_76003__boxed_3108_ = lean_unbox(v_binderInfo_3096_);
v_res_3109_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0(v_body_3092_, v_binderType_3093_, v_a_3094_, v_binderName_3095_, v_binderInfo_76003__boxed_3108_, v_e_3097_, v_x_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec_ref(v_x_3098_);
lean_dec_ref(v_binderType_3093_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0(lean_object* v_body_3110_, lean_object* v_binderType_3111_, lean_object* v_a_3112_, lean_object* v_binderName_3113_, uint8_t v_binderInfo_3114_, lean_object* v_e_3115_, lean_object* v_x_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
lean_object* v___x_3126_; 
lean_inc_ref(v_body_3110_);
v___x_3126_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(v_body_3110_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3142_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3129_ = v___x_3126_;
v_isShared_3130_ = v_isSharedCheck_3142_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3126_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3142_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
size_t v___x_3131_; size_t v___x_3132_; uint8_t v___x_3133_; 
v___x_3131_ = lean_ptr_addr(v_binderType_3111_);
v___x_3132_ = lean_ptr_addr(v_a_3112_);
v___x_3133_ = lean_usize_dec_eq(v___x_3131_, v___x_3132_);
if (v___x_3133_ == 0)
{
lean_object* v___x_3134_; 
lean_del_object(v___x_3129_);
lean_dec_ref(v_e_3115_);
lean_dec_ref(v_body_3110_);
v___x_3134_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(v_binderName_3113_, v_binderInfo_3114_, v_a_3112_, v_a_3127_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
return v___x_3134_;
}
else
{
size_t v___x_3135_; size_t v___x_3136_; uint8_t v___x_3137_; 
v___x_3135_ = lean_ptr_addr(v_body_3110_);
lean_dec_ref(v_body_3110_);
v___x_3136_ = lean_ptr_addr(v_a_3127_);
v___x_3137_ = lean_usize_dec_eq(v___x_3135_, v___x_3136_);
if (v___x_3137_ == 0)
{
lean_object* v___x_3138_; 
lean_del_object(v___x_3129_);
lean_dec_ref(v_e_3115_);
v___x_3138_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(v_binderName_3113_, v_binderInfo_3114_, v_a_3112_, v_a_3127_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
return v___x_3138_;
}
else
{
lean_object* v___x_3140_; 
lean_dec(v_a_3127_);
lean_dec(v_binderName_3113_);
lean_dec_ref(v_a_3112_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v_e_3115_);
v___x_3140_ = v___x_3129_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_e_3115_);
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
lean_dec_ref(v_e_3115_);
lean_dec(v_binderName_3113_);
lean_dec_ref(v_a_3112_);
lean_dec_ref(v_body_3110_);
return v___x_3126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0___boxed(lean_object* v_body_3143_, lean_object* v_binderType_3144_, lean_object* v_a_3145_, lean_object* v_binderName_3146_, lean_object* v_binderInfo_3147_, lean_object* v_e_3148_, lean_object* v_x_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
uint8_t v_binderInfo_76030__boxed_3159_; lean_object* v_res_3160_; 
v_binderInfo_76030__boxed_3159_ = lean_unbox(v_binderInfo_3147_);
v_res_3160_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0(v_body_3143_, v_binderType_3144_, v_a_3145_, v_binderName_3146_, v_binderInfo_76030__boxed_3159_, v_e_3148_, v_x_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec_ref(v_x_3149_);
lean_dec_ref(v_binderType_3144_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(lean_object* v_e_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_){
_start:
{
if (lean_obj_tag(v_e_3161_) == 7)
{
lean_object* v_binderName_3171_; lean_object* v_binderType_3172_; lean_object* v_body_3173_; uint8_t v_binderInfo_3174_; lean_object* v___x_3175_; 
v_binderName_3171_ = lean_ctor_get(v_e_3161_, 0);
lean_inc(v_binderName_3171_);
v_binderType_3172_ = lean_ctor_get(v_e_3161_, 1);
lean_inc_ref_n(v_binderType_3172_, 2);
v_body_3173_ = lean_ctor_get(v_e_3161_, 2);
lean_inc_ref(v_body_3173_);
v_binderInfo_3174_ = lean_ctor_get_uint8(v_e_3161_, sizeof(void*)*3 + 8);
v___x_3175_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_binderType_3172_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_object* v_a_3176_; lean_object* v___x_3177_; 
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
lean_inc_n(v_a_3176_, 2);
lean_dec_ref_known(v___x_3175_, 1);
v___x_3177_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3176_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3179_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
lean_inc_n(v_a_3178_, 2);
lean_dec_ref_known(v___x_3177_, 1);
v___x_3179_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_binderType_3172_, v_a_3178_, v_a_3162_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_cleanSuffix_3180_; lean_object* v___x_3181_; lean_object* v___f_3182_; lean_object* v___x_3183_; uint8_t v___y_3185_; lean_object* v___x_3188_; uint8_t v___x_3189_; 
lean_dec_ref_known(v___x_3179_, 1);
v_cleanSuffix_3180_ = lean_ctor_get(v_a_3162_, 2);
v___x_3181_ = lean_box(v_binderInfo_3174_);
lean_inc(v_binderName_3171_);
lean_inc_ref(v_binderType_3172_);
v___f_3182_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0___boxed), 16, 6);
lean_closure_set(v___f_3182_, 0, v_body_3173_);
lean_closure_set(v___f_3182_, 1, v_binderType_3172_);
lean_closure_set(v___f_3182_, 2, v_a_3176_);
lean_closure_set(v___f_3182_, 3, v_binderName_3171_);
lean_closure_set(v___f_3182_, 4, v___x_3181_);
lean_closure_set(v___f_3182_, 5, v_e_3161_);
v___x_3183_ = lean_box(0);
v___x_3188_ = l_Lean_Expr_looseBVarRange(v_binderType_3172_);
lean_dec_ref(v_binderType_3172_);
v___x_3189_ = lean_nat_dec_le(v___x_3188_, v_cleanSuffix_3180_);
lean_dec(v___x_3188_);
if (v___x_3189_ == 0)
{
uint8_t v___x_3190_; 
v___x_3190_ = 1;
v___y_3185_ = v___x_3190_;
goto v___jp_3184_;
}
else
{
uint8_t v___x_3191_; 
v___x_3191_ = 0;
v___y_3185_ = v___x_3191_;
goto v___jp_3184_;
}
v___jp_3184_:
{
uint8_t v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = 0;
v___x_3187_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_binderName_3171_, v_a_3178_, v___x_3183_, v___y_3185_, v___x_3186_, v___f_3182_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
return v___x_3187_;
}
}
else
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
lean_dec(v_a_3178_);
lean_dec(v_a_3176_);
lean_dec_ref(v_body_3173_);
lean_dec_ref(v_binderType_3172_);
lean_dec(v_binderName_3171_);
lean_dec_ref_known(v_e_3161_, 3);
v_a_3192_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_3179_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3179_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
else
{
lean_dec(v_a_3176_);
lean_dec_ref(v_body_3173_);
lean_dec_ref(v_binderType_3172_);
lean_dec_ref_known(v_e_3161_, 3);
lean_dec(v_binderName_3171_);
return v___x_3177_;
}
}
else
{
lean_dec_ref(v_body_3173_);
lean_dec_ref(v_binderType_3172_);
lean_dec_ref_known(v_e_3161_, 3);
lean_dec(v_binderName_3171_);
return v___x_3175_;
}
}
else
{
lean_object* v___x_3200_; 
lean_inc_ref(v_e_3161_);
v___x_3200_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_e_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v_numCandidates_3202_; lean_object* v_cleanSuffix_3203_; lean_object* v___x_3204_; uint8_t v___x_3205_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_a_3201_);
v_numCandidates_3202_ = lean_ctor_get(v_a_3162_, 1);
v_cleanSuffix_3203_ = lean_ctor_get(v_a_3162_, 2);
v___x_3204_ = lean_unsigned_to_nat(0u);
v___x_3205_ = lean_nat_dec_lt(v___x_3204_, v_numCandidates_3202_);
if (v___x_3205_ == 0)
{
lean_dec(v_a_3201_);
lean_dec_ref(v_e_3161_);
return v___x_3200_;
}
else
{
lean_object* v___x_3206_; uint8_t v___x_3207_; 
v___x_3206_ = l_Lean_Expr_looseBVarRange(v_e_3161_);
lean_dec_ref(v_e_3161_);
v___x_3207_ = lean_nat_dec_le(v___x_3206_, v_cleanSuffix_3203_);
lean_dec(v___x_3206_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3208_; 
lean_dec_ref_known(v___x_3200_, 1);
lean_inc(v_a_3201_);
v___x_3208_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3201_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3210_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
lean_inc(v_a_3209_);
lean_dec_ref_known(v___x_3208_, 1);
v___x_3210_ = l_Lean_Meta_getLevel(v_a_3209_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3217_ == 0)
{
lean_object* v_unused_3218_; 
v_unused_3218_ = lean_ctor_get(v___x_3210_, 0);
lean_dec(v_unused_3218_);
v___x_3212_ = v___x_3210_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_dec(v___x_3210_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 0, v_a_3201_);
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3201_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec(v_a_3201_);
v_a_3219_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3210_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3210_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
else
{
lean_dec(v_a_3201_);
return v___x_3208_;
}
}
else
{
lean_dec(v_a_3201_);
return v___x_3200_;
}
}
}
else
{
lean_dec_ref(v_e_3161_);
return v___x_3200_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1(lean_object* v_body_3227_, lean_object* v_type_3228_, lean_object* v_a_3229_, lean_object* v_declName_3230_, lean_object* v_a_3231_, uint8_t v_nondep_3232_, lean_object* v_value_3233_, lean_object* v_e_3234_, uint8_t v___y_3235_, lean_object* v_x_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v___x_3246_; 
lean_inc_ref(v_body_3227_);
v___x_3246_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_body_3227_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3313_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3249_ = v___x_3246_;
v_isShared_3250_ = v_isSharedCheck_3313_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3246_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3313_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; uint8_t v_nondep_x27_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___x_3283_; 
v___x_3283_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v___y_3242_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_a_3284_; uint8_t v___x_3285_; 
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
lean_inc(v_a_3284_);
lean_dec_ref_known(v___x_3283_, 1);
v___x_3285_ = 1;
if (v_nondep_3232_ == 0)
{
if (v___y_3235_ == 0)
{
lean_dec(v_a_3284_);
v_nondep_x27_3274_ = v_nondep_3232_;
v___y_3275_ = v___y_3239_;
v___y_3276_ = v___y_3240_;
v___y_3277_ = v___y_3241_;
v___y_3278_ = v___y_3242_;
v___y_3279_ = v___y_3243_;
v___y_3280_ = v___y_3244_;
goto v___jp_3273_;
}
else
{
lean_object* v___x_3286_; uint8_t v___x_3287_; 
v___x_3286_ = l_Lean_Expr_fvarId_x21(v_x_3236_);
v___x_3287_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(v___x_3286_, v_a_3284_);
lean_dec(v_a_3284_);
lean_dec(v___x_3286_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; lean_object* v_visited_3289_; lean_object* v_types_3290_; lean_object* v_subst_3291_; lean_object* v_visitedClosed_3292_; lean_object* v_hasDepLetCache_3293_; lean_object* v_numConverted_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3304_; 
v___x_3288_ = lean_st_ref_take(v___y_3238_);
v_visited_3289_ = lean_ctor_get(v___x_3288_, 0);
v_types_3290_ = lean_ctor_get(v___x_3288_, 1);
v_subst_3291_ = lean_ctor_get(v___x_3288_, 2);
v_visitedClosed_3292_ = lean_ctor_get(v___x_3288_, 3);
v_hasDepLetCache_3293_ = lean_ctor_get(v___x_3288_, 4);
v_numConverted_3294_ = lean_ctor_get(v___x_3288_, 5);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3296_ = v___x_3288_;
v_isShared_3297_ = v_isSharedCheck_3304_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_numConverted_3294_);
lean_inc(v_hasDepLetCache_3293_);
lean_inc(v_visitedClosed_3292_);
lean_inc(v_subst_3291_);
lean_inc(v_types_3290_);
lean_inc(v_visited_3289_);
lean_dec(v___x_3288_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3304_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3301_; 
v___x_3298_ = lean_unsigned_to_nat(1u);
v___x_3299_ = lean_nat_add(v_numConverted_3294_, v___x_3298_);
lean_dec(v_numConverted_3294_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 5, v___x_3299_);
v___x_3301_ = v___x_3296_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_visited_3289_);
lean_ctor_set(v_reuseFailAlloc_3303_, 1, v_types_3290_);
lean_ctor_set(v_reuseFailAlloc_3303_, 2, v_subst_3291_);
lean_ctor_set(v_reuseFailAlloc_3303_, 3, v_visitedClosed_3292_);
lean_ctor_set(v_reuseFailAlloc_3303_, 4, v_hasDepLetCache_3293_);
lean_ctor_set(v_reuseFailAlloc_3303_, 5, v___x_3299_);
v___x_3301_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
lean_object* v___x_3302_; 
v___x_3302_ = lean_st_ref_put(v___y_3238_, v___x_3301_);
v_nondep_x27_3274_ = v___x_3285_;
v___y_3275_ = v___y_3239_;
v___y_3276_ = v___y_3240_;
v___y_3277_ = v___y_3241_;
v___y_3278_ = v___y_3242_;
v___y_3279_ = v___y_3243_;
v___y_3280_ = v___y_3244_;
goto v___jp_3273_;
}
}
}
else
{
v_nondep_x27_3274_ = v_nondep_3232_;
v___y_3275_ = v___y_3239_;
v___y_3276_ = v___y_3240_;
v___y_3277_ = v___y_3241_;
v___y_3278_ = v___y_3242_;
v___y_3279_ = v___y_3243_;
v___y_3280_ = v___y_3244_;
goto v___jp_3273_;
}
}
}
else
{
lean_dec(v_a_3284_);
v_nondep_x27_3274_ = v___x_3285_;
v___y_3275_ = v___y_3239_;
v___y_3276_ = v___y_3240_;
v___y_3277_ = v___y_3241_;
v___y_3278_ = v___y_3242_;
v___y_3279_ = v___y_3243_;
v___y_3280_ = v___y_3244_;
goto v___jp_3273_;
}
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
lean_del_object(v___x_3249_);
lean_dec(v_a_3247_);
lean_dec_ref(v_e_3234_);
lean_dec_ref(v_a_3231_);
lean_dec(v_declName_3230_);
lean_dec_ref(v_a_3229_);
lean_dec_ref(v_body_3227_);
v_a_3305_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3283_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3283_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3310_; 
if (v_isShared_3308_ == 0)
{
v___x_3310_ = v___x_3307_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
v___jp_3251_:
{
size_t v___x_3258_; size_t v___x_3259_; uint8_t v___x_3260_; 
v___x_3258_ = lean_ptr_addr(v_type_3228_);
v___x_3259_ = lean_ptr_addr(v_a_3229_);
v___x_3260_ = lean_usize_dec_eq(v___x_3258_, v___x_3259_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3261_; 
lean_del_object(v___x_3249_);
lean_dec_ref(v_e_3234_);
lean_dec_ref(v_body_3227_);
v___x_3261_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3230_, v_a_3229_, v_a_3231_, v_a_3247_, v_nondep_3232_, v___y_3255_, v___y_3252_, v___y_3256_, v___y_3254_, v___y_3257_, v___y_3253_);
return v___x_3261_;
}
else
{
size_t v___x_3262_; size_t v___x_3263_; uint8_t v___x_3264_; 
v___x_3262_ = lean_ptr_addr(v_value_3233_);
v___x_3263_ = lean_ptr_addr(v_a_3231_);
v___x_3264_ = lean_usize_dec_eq(v___x_3262_, v___x_3263_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3265_; 
lean_del_object(v___x_3249_);
lean_dec_ref(v_e_3234_);
lean_dec_ref(v_body_3227_);
v___x_3265_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3230_, v_a_3229_, v_a_3231_, v_a_3247_, v_nondep_3232_, v___y_3255_, v___y_3252_, v___y_3256_, v___y_3254_, v___y_3257_, v___y_3253_);
return v___x_3265_;
}
else
{
size_t v___x_3266_; size_t v___x_3267_; uint8_t v___x_3268_; 
v___x_3266_ = lean_ptr_addr(v_body_3227_);
lean_dec_ref(v_body_3227_);
v___x_3267_ = lean_ptr_addr(v_a_3247_);
v___x_3268_ = lean_usize_dec_eq(v___x_3266_, v___x_3267_);
if (v___x_3268_ == 0)
{
lean_object* v___x_3269_; 
lean_del_object(v___x_3249_);
lean_dec_ref(v_e_3234_);
v___x_3269_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3230_, v_a_3229_, v_a_3231_, v_a_3247_, v_nondep_3232_, v___y_3255_, v___y_3252_, v___y_3256_, v___y_3254_, v___y_3257_, v___y_3253_);
return v___x_3269_;
}
else
{
lean_object* v___x_3271_; 
lean_dec(v_a_3247_);
lean_dec_ref(v_a_3231_);
lean_dec(v_declName_3230_);
lean_dec_ref(v_a_3229_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v_e_3234_);
v___x_3271_ = v___x_3249_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_e_3234_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
}
v___jp_3273_:
{
if (v_nondep_3232_ == 0)
{
if (v_nondep_x27_3274_ == 0)
{
v___y_3252_ = v___y_3276_;
v___y_3253_ = v___y_3280_;
v___y_3254_ = v___y_3278_;
v___y_3255_ = v___y_3275_;
v___y_3256_ = v___y_3277_;
v___y_3257_ = v___y_3279_;
goto v___jp_3251_;
}
else
{
lean_object* v___x_3281_; 
lean_del_object(v___x_3249_);
lean_dec_ref(v_e_3234_);
lean_dec_ref(v_body_3227_);
v___x_3281_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3230_, v_a_3229_, v_a_3231_, v_a_3247_, v_nondep_x27_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
return v___x_3281_;
}
}
else
{
if (v_nondep_x27_3274_ == 0)
{
lean_object* v___x_3282_; 
lean_del_object(v___x_3249_);
lean_dec_ref(v_e_3234_);
lean_dec_ref(v_body_3227_);
v___x_3282_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3230_, v_a_3229_, v_a_3231_, v_a_3247_, v_nondep_x27_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
return v___x_3282_;
}
else
{
v___y_3252_ = v___y_3276_;
v___y_3253_ = v___y_3280_;
v___y_3254_ = v___y_3278_;
v___y_3255_ = v___y_3275_;
v___y_3256_ = v___y_3277_;
v___y_3257_ = v___y_3279_;
goto v___jp_3251_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3234_);
lean_dec_ref(v_a_3231_);
lean_dec(v_declName_3230_);
lean_dec_ref(v_a_3229_);
lean_dec_ref(v_body_3227_);
return v___x_3246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1___boxed(lean_object** _args){
lean_object* v_body_3314_ = _args[0];
lean_object* v_type_3315_ = _args[1];
lean_object* v_a_3316_ = _args[2];
lean_object* v_declName_3317_ = _args[3];
lean_object* v_a_3318_ = _args[4];
lean_object* v_nondep_3319_ = _args[5];
lean_object* v_value_3320_ = _args[6];
lean_object* v_e_3321_ = _args[7];
lean_object* v___y_3322_ = _args[8];
lean_object* v_x_3323_ = _args[9];
lean_object* v___y_3324_ = _args[10];
lean_object* v___y_3325_ = _args[11];
lean_object* v___y_3326_ = _args[12];
lean_object* v___y_3327_ = _args[13];
lean_object* v___y_3328_ = _args[14];
lean_object* v___y_3329_ = _args[15];
lean_object* v___y_3330_ = _args[16];
lean_object* v___y_3331_ = _args[17];
lean_object* v___y_3332_ = _args[18];
_start:
{
uint8_t v_nondep_76186__boxed_3333_; uint8_t v___y_76188__boxed_3334_; lean_object* v_res_3335_; 
v_nondep_76186__boxed_3333_ = lean_unbox(v_nondep_3319_);
v___y_76188__boxed_3334_ = lean_unbox(v___y_3322_);
v_res_3335_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1(v_body_3314_, v_type_3315_, v_a_3316_, v_declName_3317_, v_a_3318_, v_nondep_76186__boxed_3333_, v_value_3320_, v_e_3321_, v___y_76188__boxed_3334_, v_x_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec_ref(v_x_3323_);
lean_dec_ref(v_value_3320_);
lean_dec_ref(v_type_3315_);
return v_res_3335_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1(void){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3337_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_3338_ = lean_unsigned_to_nat(9u);
v___x_3339_ = lean_unsigned_to_nat(263u);
v___x_3340_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__0));
v___x_3341_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0));
v___x_3342_ = l_mkPanicMessageWithDecl(v___x_3341_, v___x_3340_, v___x_3339_, v___x_3338_, v___x_3337_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(lean_object* v_e_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_){
_start:
{
switch(lean_obj_tag(v_e_3343_))
{
case 5:
{
lean_object* v_fn_3353_; lean_object* v_arg_3354_; lean_object* v___y_3356_; lean_object* v_a_3357_; lean_object* v___y_3379_; lean_object* v___x_3381_; 
v_fn_3353_ = lean_ctor_get(v_e_3343_, 0);
lean_inc_ref_n(v_fn_3353_, 2);
v_arg_3354_ = lean_ctor_get(v_e_3343_, 1);
lean_inc_ref(v_arg_3354_);
v___x_3381_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_fn_3353_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3383_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
lean_dec_ref_known(v___x_3381_, 1);
lean_inc_ref(v_arg_3354_);
v___x_3383_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_arg_3354_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3399_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3386_ = v___x_3383_;
v_isShared_3387_ = v_isSharedCheck_3399_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3383_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3399_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
size_t v___x_3388_; size_t v___x_3389_; uint8_t v___x_3390_; 
v___x_3388_ = lean_ptr_addr(v_fn_3353_);
v___x_3389_ = lean_ptr_addr(v_a_3382_);
v___x_3390_ = lean_usize_dec_eq(v___x_3388_, v___x_3389_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3391_; 
lean_del_object(v___x_3386_);
lean_dec_ref_known(v_e_3343_, 2);
v___x_3391_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(v_a_3382_, v_a_3384_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
v___y_3379_ = v___x_3391_;
goto v___jp_3378_;
}
else
{
size_t v___x_3392_; size_t v___x_3393_; uint8_t v___x_3394_; 
v___x_3392_ = lean_ptr_addr(v_arg_3354_);
v___x_3393_ = lean_ptr_addr(v_a_3384_);
v___x_3394_ = lean_usize_dec_eq(v___x_3392_, v___x_3393_);
if (v___x_3394_ == 0)
{
lean_object* v___x_3395_; 
lean_del_object(v___x_3386_);
lean_dec_ref_known(v_e_3343_, 2);
v___x_3395_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(v_a_3382_, v_a_3384_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
v___y_3379_ = v___x_3395_;
goto v___jp_3378_;
}
else
{
lean_object* v___x_3397_; 
lean_dec(v_a_3384_);
lean_dec(v_a_3382_);
lean_inc_ref(v_e_3343_);
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 0, v_e_3343_);
v___x_3397_ = v___x_3386_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_e_3343_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
v___y_3356_ = v___x_3397_;
v_a_3357_ = v_e_3343_;
goto v___jp_3355_;
}
}
}
}
}
else
{
lean_dec(v_a_3382_);
lean_dec_ref(v_arg_3354_);
lean_dec_ref_known(v_e_3343_, 2);
lean_dec_ref(v_fn_3353_);
return v___x_3383_;
}
}
else
{
lean_dec_ref(v_arg_3354_);
lean_dec_ref_known(v_e_3343_, 2);
lean_dec_ref(v_fn_3353_);
return v___x_3381_;
}
v___jp_3355_:
{
lean_object* v_numCandidates_3358_; lean_object* v___x_3359_; uint8_t v___x_3360_; 
v_numCandidates_3358_ = lean_ctor_get(v_a_3344_, 1);
v___x_3359_ = lean_unsigned_to_nat(0u);
v___x_3360_ = lean_nat_dec_lt(v___x_3359_, v_numCandidates_3358_);
if (v___x_3360_ == 0)
{
lean_dec_ref(v_a_3357_);
lean_dec_ref(v_arg_3354_);
lean_dec_ref(v_fn_3353_);
return v___y_3356_;
}
else
{
lean_object* v___x_3361_; 
lean_dec_ref(v___y_3356_);
v___x_3361_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp(v_fn_3353_, v_arg_3354_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3368_ == 0)
{
lean_object* v_unused_3369_; 
v_unused_3369_ = lean_ctor_get(v___x_3361_, 0);
lean_dec(v_unused_3369_);
v___x_3363_ = v___x_3361_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_dec(v___x_3361_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 0, v_a_3357_);
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3357_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
else
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3377_; 
lean_dec_ref(v_a_3357_);
v_a_3370_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3372_ = v___x_3361_;
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3361_);
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
}
}
v___jp_3378_:
{
if (lean_obj_tag(v___y_3379_) == 0)
{
lean_object* v_a_3380_; 
v_a_3380_ = lean_ctor_get(v___y_3379_, 0);
lean_inc(v_a_3380_);
v___y_3356_ = v___y_3379_;
v_a_3357_ = v_a_3380_;
goto v___jp_3355_;
}
else
{
lean_dec_ref(v_arg_3354_);
lean_dec_ref(v_fn_3353_);
return v___y_3379_;
}
}
}
case 10:
{
lean_object* v_data_3400_; lean_object* v_expr_3401_; lean_object* v___x_3402_; 
v_data_3400_ = lean_ctor_get(v_e_3343_, 0);
v_expr_3401_ = lean_ctor_get(v_e_3343_, 1);
lean_inc_ref(v_expr_3401_);
v___x_3402_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_expr_3401_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3414_; 
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3405_ = v___x_3402_;
v_isShared_3406_ = v_isSharedCheck_3414_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3402_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3414_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
size_t v___x_3407_; size_t v___x_3408_; uint8_t v___x_3409_; 
v___x_3407_ = lean_ptr_addr(v_expr_3401_);
v___x_3408_ = lean_ptr_addr(v_a_3403_);
v___x_3409_ = lean_usize_dec_eq(v___x_3407_, v___x_3408_);
if (v___x_3409_ == 0)
{
lean_object* v___x_3410_; 
lean_inc(v_data_3400_);
lean_del_object(v___x_3405_);
lean_dec_ref_known(v_e_3343_, 2);
v___x_3410_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(v_data_3400_, v_a_3403_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
return v___x_3410_;
}
else
{
lean_object* v___x_3412_; 
lean_dec(v_a_3403_);
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 0, v_e_3343_);
v___x_3412_ = v___x_3405_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_e_3343_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3343_, 2);
return v___x_3402_;
}
}
case 11:
{
lean_object* v_typeName_3415_; lean_object* v_idx_3416_; lean_object* v_struct_3417_; lean_object* v___y_3419_; lean_object* v_a_3420_; lean_object* v___x_3436_; 
v_typeName_3415_ = lean_ctor_get(v_e_3343_, 0);
v_idx_3416_ = lean_ctor_get(v_e_3343_, 1);
v_struct_3417_ = lean_ctor_get(v_e_3343_, 2);
lean_inc_ref(v_struct_3417_);
v___x_3436_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_struct_3417_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3449_; 
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3439_ = v___x_3436_;
v_isShared_3440_ = v_isSharedCheck_3449_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3436_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3449_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
size_t v___x_3441_; size_t v___x_3442_; uint8_t v___x_3443_; 
v___x_3441_ = lean_ptr_addr(v_struct_3417_);
v___x_3442_ = lean_ptr_addr(v_a_3437_);
v___x_3443_ = lean_usize_dec_eq(v___x_3441_, v___x_3442_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; 
lean_del_object(v___x_3439_);
lean_inc(v_idx_3416_);
lean_inc(v_typeName_3415_);
v___x_3444_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(v_typeName_3415_, v_idx_3416_, v_a_3437_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3445_);
v___y_3419_ = v___x_3444_;
v_a_3420_ = v_a_3445_;
goto v___jp_3418_;
}
else
{
lean_dec_ref_known(v_e_3343_, 3);
return v___x_3444_;
}
}
else
{
lean_object* v___x_3447_; 
lean_dec(v_a_3437_);
lean_inc_ref(v_e_3343_);
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 0, v_e_3343_);
v___x_3447_ = v___x_3439_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_e_3343_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
lean_inc_ref(v_e_3343_);
v___y_3419_ = v___x_3447_;
v_a_3420_ = v_e_3343_;
goto v___jp_3418_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3343_, 3);
return v___x_3436_;
}
v___jp_3418_:
{
lean_object* v_numCandidates_3421_; lean_object* v_cleanSuffix_3422_; lean_object* v___x_3423_; uint8_t v___x_3424_; 
v_numCandidates_3421_ = lean_ctor_get(v_a_3344_, 1);
v_cleanSuffix_3422_ = lean_ctor_get(v_a_3344_, 2);
v___x_3423_ = lean_unsigned_to_nat(0u);
v___x_3424_ = lean_nat_dec_lt(v___x_3423_, v_numCandidates_3421_);
if (v___x_3424_ == 0)
{
lean_dec_ref(v_a_3420_);
lean_dec_ref_known(v_e_3343_, 3);
return v___y_3419_;
}
else
{
lean_object* v___x_3425_; uint8_t v___x_3426_; 
v___x_3425_ = l_Lean_Expr_looseBVarRange(v_struct_3417_);
v___x_3426_ = lean_nat_dec_le(v___x_3425_, v_cleanSuffix_3422_);
lean_dec(v___x_3425_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; 
lean_dec_ref(v___y_3419_);
v___x_3427_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(v_e_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
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
lean_ctor_set(v___x_3429_, 0, v_a_3420_);
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3420_);
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
lean_dec_ref(v_a_3420_);
return v___x_3427_;
}
}
else
{
lean_dec_ref(v_a_3420_);
lean_dec_ref_known(v_e_3343_, 3);
return v___y_3419_;
}
}
}
}
case 6:
{
lean_object* v_binderName_3450_; lean_object* v_binderType_3451_; lean_object* v_body_3452_; uint8_t v_binderInfo_3453_; lean_object* v___x_3454_; 
v_binderName_3450_ = lean_ctor_get(v_e_3343_, 0);
lean_inc(v_binderName_3450_);
v_binderType_3451_ = lean_ctor_get(v_e_3343_, 1);
lean_inc_ref_n(v_binderType_3451_, 2);
v_body_3452_ = lean_ctor_get(v_e_3343_, 2);
lean_inc_ref(v_body_3452_);
v_binderInfo_3453_ = lean_ctor_get_uint8(v_e_3343_, sizeof(void*)*3 + 8);
v___x_3454_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_binderType_3451_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3456_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
lean_inc_n(v_a_3455_, 2);
lean_dec_ref_known(v___x_3454_, 1);
v___x_3456_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3455_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3458_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc_n(v_a_3457_, 2);
lean_dec_ref_known(v___x_3456_, 1);
v___x_3458_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_binderType_3451_, v_a_3457_, v_a_3344_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_cleanSuffix_3459_; lean_object* v___x_3460_; lean_object* v___f_3461_; lean_object* v___x_3462_; uint8_t v___y_3464_; lean_object* v___x_3467_; uint8_t v___x_3468_; 
lean_dec_ref_known(v___x_3458_, 1);
v_cleanSuffix_3459_ = lean_ctor_get(v_a_3344_, 2);
v___x_3460_ = lean_box(v_binderInfo_3453_);
lean_inc(v_binderName_3450_);
lean_inc_ref(v_binderType_3451_);
v___f_3461_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0___boxed), 16, 6);
lean_closure_set(v___f_3461_, 0, v_body_3452_);
lean_closure_set(v___f_3461_, 1, v_binderType_3451_);
lean_closure_set(v___f_3461_, 2, v_a_3455_);
lean_closure_set(v___f_3461_, 3, v_binderName_3450_);
lean_closure_set(v___f_3461_, 4, v___x_3460_);
lean_closure_set(v___f_3461_, 5, v_e_3343_);
v___x_3462_ = lean_box(0);
v___x_3467_ = l_Lean_Expr_looseBVarRange(v_binderType_3451_);
lean_dec_ref(v_binderType_3451_);
v___x_3468_ = lean_nat_dec_le(v___x_3467_, v_cleanSuffix_3459_);
lean_dec(v___x_3467_);
if (v___x_3468_ == 0)
{
uint8_t v___x_3469_; 
v___x_3469_ = 1;
v___y_3464_ = v___x_3469_;
goto v___jp_3463_;
}
else
{
uint8_t v___x_3470_; 
v___x_3470_ = 0;
v___y_3464_ = v___x_3470_;
goto v___jp_3463_;
}
v___jp_3463_:
{
uint8_t v___x_3465_; lean_object* v___x_3466_; 
v___x_3465_ = 0;
v___x_3466_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_binderName_3450_, v_a_3457_, v___x_3462_, v___y_3464_, v___x_3465_, v___f_3461_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
return v___x_3466_;
}
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec(v_a_3457_);
lean_dec(v_a_3455_);
lean_dec_ref(v_body_3452_);
lean_dec_ref(v_binderType_3451_);
lean_dec_ref_known(v_e_3343_, 3);
lean_dec(v_binderName_3450_);
v_a_3471_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3458_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3458_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
else
{
lean_dec(v_a_3455_);
lean_dec_ref(v_body_3452_);
lean_dec_ref(v_binderType_3451_);
lean_dec_ref_known(v_e_3343_, 3);
lean_dec(v_binderName_3450_);
return v___x_3456_;
}
}
else
{
lean_dec_ref(v_body_3452_);
lean_dec_ref(v_binderType_3451_);
lean_dec_ref_known(v_e_3343_, 3);
lean_dec(v_binderName_3450_);
return v___x_3454_;
}
}
case 7:
{
lean_object* v___x_3479_; 
v___x_3479_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(v_e_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
return v___x_3479_;
}
case 8:
{
lean_object* v_declName_3480_; lean_object* v_type_3481_; lean_object* v_value_3482_; lean_object* v_body_3483_; uint8_t v_nondep_3484_; lean_object* v___x_3485_; 
v_declName_3480_ = lean_ctor_get(v_e_3343_, 0);
lean_inc(v_declName_3480_);
v_type_3481_ = lean_ctor_get(v_e_3343_, 1);
lean_inc_ref_n(v_type_3481_, 2);
v_value_3482_ = lean_ctor_get(v_e_3343_, 2);
lean_inc_ref(v_value_3482_);
v_body_3483_ = lean_ctor_get(v_e_3343_, 3);
lean_inc_ref(v_body_3483_);
v_nondep_3484_ = lean_ctor_get_uint8(v_e_3343_, sizeof(void*)*4 + 8);
v___x_3485_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_type_3481_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3487_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v___x_3485_, 1);
lean_inc_ref(v_value_3482_);
v___x_3487_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_value_3482_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3489_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v___x_3487_, 1);
lean_inc(v_a_3486_);
v___x_3489_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3486_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3574_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3492_ = v___x_3489_;
v_isShared_3493_ = v_isSharedCheck_3574_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3489_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3574_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v_numCandidates_3494_; lean_object* v_cleanSuffix_3495_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; uint8_t v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; uint8_t v___y_3507_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___x_3537_; uint8_t v___x_3538_; 
v_numCandidates_3494_ = lean_ctor_get(v_a_3344_, 1);
v_cleanSuffix_3495_ = lean_ctor_get(v_a_3344_, 2);
v___x_3537_ = lean_unsigned_to_nat(0u);
v___x_3538_ = lean_nat_dec_lt(v___x_3537_, v_numCandidates_3494_);
if (v___x_3538_ == 0)
{
v___y_3523_ = v_a_3344_;
v___y_3524_ = v_a_3345_;
v___y_3525_ = v_a_3346_;
v___y_3526_ = v_a_3347_;
v___y_3527_ = v_a_3348_;
v___y_3528_ = v_a_3349_;
v___y_3529_ = v_a_3350_;
v___y_3530_ = v_a_3351_;
goto v___jp_3522_;
}
else
{
lean_object* v___x_3539_; 
lean_inc(v_a_3490_);
v___x_3539_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_type_3481_, v_a_3490_, v_a_3344_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v___x_3562_; uint8_t v___x_3563_; 
lean_dec_ref_known(v___x_3539_, 1);
v___x_3562_ = l_Lean_Expr_looseBVarRange(v_type_3481_);
v___x_3563_ = lean_nat_dec_le(v___x_3562_, v_cleanSuffix_3495_);
lean_dec(v___x_3562_);
if (v___x_3563_ == 0)
{
goto v___jp_3540_;
}
else
{
lean_object* v___x_3564_; uint8_t v___x_3565_; 
v___x_3564_ = l_Lean_Expr_looseBVarRange(v_value_3482_);
v___x_3565_ = lean_nat_dec_le(v___x_3564_, v_cleanSuffix_3495_);
lean_dec(v___x_3564_);
if (v___x_3565_ == 0)
{
goto v___jp_3540_;
}
else
{
v___y_3523_ = v_a_3344_;
v___y_3524_ = v_a_3345_;
v___y_3525_ = v_a_3346_;
v___y_3526_ = v_a_3347_;
v___y_3527_ = v_a_3348_;
v___y_3528_ = v_a_3349_;
v___y_3529_ = v_a_3350_;
v___y_3530_ = v_a_3351_;
goto v___jp_3522_;
}
}
v___jp_3540_:
{
uint8_t v___x_3541_; 
v___x_3541_ = l_Lean_Expr_isLambda(v_value_3482_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3542_; 
lean_inc_ref(v_value_3482_);
v___x_3542_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_value_3482_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v_a_3543_; lean_object* v___x_3544_; 
v_a_3543_ = lean_ctor_get(v___x_3542_, 0);
lean_inc(v_a_3543_);
lean_dec_ref_known(v___x_3542_, 1);
lean_inc(v_a_3490_);
v___x_3544_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_a_3543_, v_a_3490_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_dec_ref_known(v___x_3544_, 1);
v___y_3523_ = v_a_3344_;
v___y_3524_ = v_a_3345_;
v___y_3525_ = v_a_3346_;
v___y_3526_ = v_a_3347_;
v___y_3527_ = v_a_3348_;
v___y_3528_ = v_a_3349_;
v___y_3529_ = v_a_3350_;
v___y_3530_ = v_a_3351_;
goto v___jp_3522_;
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_del_object(v___x_3492_);
lean_dec(v_a_3490_);
lean_dec(v_a_3488_);
lean_dec(v_a_3486_);
lean_dec_ref(v_body_3483_);
lean_dec_ref(v_value_3482_);
lean_dec_ref(v_type_3481_);
lean_dec_ref_known(v_e_3343_, 4);
lean_dec(v_declName_3480_);
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3544_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3544_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
else
{
lean_del_object(v___x_3492_);
lean_dec(v_a_3490_);
lean_dec(v_a_3488_);
lean_dec(v_a_3486_);
lean_dec_ref(v_body_3483_);
lean_dec_ref(v_value_3482_);
lean_dec_ref(v_type_3481_);
lean_dec_ref_known(v_e_3343_, 4);
lean_dec(v_declName_3480_);
return v___x_3542_;
}
}
else
{
lean_object* v___x_3553_; 
lean_inc(v_a_3490_);
lean_inc_ref(v_value_3482_);
v___x_3553_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_value_3482_, v_a_3490_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_dec_ref_known(v___x_3553_, 1);
v___y_3523_ = v_a_3344_;
v___y_3524_ = v_a_3345_;
v___y_3525_ = v_a_3346_;
v___y_3526_ = v_a_3347_;
v___y_3527_ = v_a_3348_;
v___y_3528_ = v_a_3349_;
v___y_3529_ = v_a_3350_;
v___y_3530_ = v_a_3351_;
goto v___jp_3522_;
}
else
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_del_object(v___x_3492_);
lean_dec(v_a_3490_);
lean_dec(v_a_3488_);
lean_dec(v_a_3486_);
lean_dec_ref(v_body_3483_);
lean_dec_ref(v_value_3482_);
lean_dec_ref(v_type_3481_);
lean_dec_ref_known(v_e_3343_, 4);
lean_dec(v_declName_3480_);
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3553_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3553_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
}
}
else
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
lean_del_object(v___x_3492_);
lean_dec(v_a_3490_);
lean_dec(v_a_3488_);
lean_dec(v_a_3486_);
lean_dec_ref(v_body_3483_);
lean_dec_ref(v_value_3482_);
lean_dec_ref(v_type_3481_);
lean_dec_ref_known(v_e_3343_, 4);
lean_dec(v_declName_3480_);
v_a_3566_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3568_ = v___x_3539_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3539_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
if (v_isShared_3569_ == 0)
{
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3566_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
v___jp_3496_:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___f_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3514_; 
v___x_3508_ = lean_box(v_nondep_3484_);
v___x_3509_ = lean_box(v___y_3507_);
lean_inc(v_declName_3480_);
lean_inc_ref(v_type_3481_);
v___f_3510_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1___boxed), 19, 9);
lean_closure_set(v___f_3510_, 0, v_body_3483_);
lean_closure_set(v___f_3510_, 1, v_type_3481_);
lean_closure_set(v___f_3510_, 2, v_a_3486_);
lean_closure_set(v___f_3510_, 3, v_declName_3480_);
lean_closure_set(v___f_3510_, 4, v_a_3488_);
lean_closure_set(v___f_3510_, 5, v___x_3508_);
lean_closure_set(v___f_3510_, 6, v_value_3482_);
lean_closure_set(v___f_3510_, 7, v_e_3343_);
lean_closure_set(v___f_3510_, 8, v___x_3509_);
v___x_3511_ = lean_box(v_nondep_3484_);
v___x_3512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3512_, 0, v___y_3503_);
lean_ctor_set(v___x_3512_, 1, v___x_3511_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set_tag(v___x_3492_, 1);
lean_ctor_set(v___x_3492_, 0, v___x_3512_);
v___x_3514_ = v___x_3492_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3512_);
v___x_3514_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
if (v___y_3500_ == 0)
{
lean_object* v___x_3515_; uint8_t v___x_3516_; 
v___x_3515_ = l_Lean_Expr_looseBVarRange(v_type_3481_);
lean_dec_ref(v_type_3481_);
v___x_3516_ = lean_nat_dec_le(v___x_3515_, v_cleanSuffix_3495_);
lean_dec(v___x_3515_);
if (v___x_3516_ == 0)
{
uint8_t v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = 1;
v___x_3518_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_declName_3480_, v_a_3490_, v___x_3514_, v___x_3517_, v___y_3507_, v___f_3510_, v___y_3497_, v___y_3502_, v___y_3505_, v___y_3498_, v___y_3499_, v___y_3506_, v___y_3501_, v___y_3504_);
return v___x_3518_;
}
else
{
lean_object* v___x_3519_; 
v___x_3519_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_declName_3480_, v_a_3490_, v___x_3514_, v___y_3500_, v___y_3507_, v___f_3510_, v___y_3497_, v___y_3502_, v___y_3505_, v___y_3498_, v___y_3499_, v___y_3506_, v___y_3501_, v___y_3504_);
return v___x_3519_;
}
}
else
{
lean_object* v___x_3520_; 
lean_dec_ref(v_type_3481_);
v___x_3520_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_declName_3480_, v_a_3490_, v___x_3514_, v___y_3500_, v___y_3507_, v___f_3510_, v___y_3497_, v___y_3502_, v___y_3505_, v___y_3498_, v___y_3499_, v___y_3506_, v___y_3501_, v___y_3504_);
return v___x_3520_;
}
}
}
v___jp_3522_:
{
lean_object* v___x_3531_; 
lean_inc(v_a_3488_);
v___x_3531_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3488_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
if (lean_obj_tag(v___x_3531_) == 0)
{
if (v_nondep_3484_ == 0)
{
lean_object* v_a_3532_; uint8_t v___x_3533_; uint8_t v___x_3534_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3532_);
lean_dec_ref_known(v___x_3531_, 1);
v___x_3533_ = 1;
v___x_3534_ = l_Lean_Expr_hasExprMVar(v_e_3343_);
if (v___x_3534_ == 0)
{
v___y_3497_ = v___y_3523_;
v___y_3498_ = v___y_3526_;
v___y_3499_ = v___y_3527_;
v___y_3500_ = v___x_3533_;
v___y_3501_ = v___y_3529_;
v___y_3502_ = v___y_3524_;
v___y_3503_ = v_a_3532_;
v___y_3504_ = v___y_3530_;
v___y_3505_ = v___y_3525_;
v___y_3506_ = v___y_3528_;
v___y_3507_ = v___x_3533_;
goto v___jp_3496_;
}
else
{
v___y_3497_ = v___y_3523_;
v___y_3498_ = v___y_3526_;
v___y_3499_ = v___y_3527_;
v___y_3500_ = v___x_3533_;
v___y_3501_ = v___y_3529_;
v___y_3502_ = v___y_3524_;
v___y_3503_ = v_a_3532_;
v___y_3504_ = v___y_3530_;
v___y_3505_ = v___y_3525_;
v___y_3506_ = v___y_3528_;
v___y_3507_ = v_nondep_3484_;
goto v___jp_3496_;
}
}
else
{
lean_object* v_a_3535_; uint8_t v___x_3536_; 
v_a_3535_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3535_);
lean_dec_ref_known(v___x_3531_, 1);
v___x_3536_ = 0;
v___y_3497_ = v___y_3523_;
v___y_3498_ = v___y_3526_;
v___y_3499_ = v___y_3527_;
v___y_3500_ = v___x_3536_;
v___y_3501_ = v___y_3529_;
v___y_3502_ = v___y_3524_;
v___y_3503_ = v_a_3535_;
v___y_3504_ = v___y_3530_;
v___y_3505_ = v___y_3525_;
v___y_3506_ = v___y_3528_;
v___y_3507_ = v___x_3536_;
goto v___jp_3496_;
}
}
else
{
lean_del_object(v___x_3492_);
lean_dec(v_a_3490_);
lean_dec(v_a_3488_);
lean_dec(v_a_3486_);
lean_dec_ref(v_body_3483_);
lean_dec_ref(v_value_3482_);
lean_dec_ref(v_type_3481_);
lean_dec_ref_known(v_e_3343_, 4);
lean_dec(v_declName_3480_);
return v___x_3531_;
}
}
}
}
else
{
lean_dec(v_a_3488_);
lean_dec(v_a_3486_);
lean_dec_ref(v_body_3483_);
lean_dec_ref(v_value_3482_);
lean_dec_ref(v_type_3481_);
lean_dec_ref_known(v_e_3343_, 4);
lean_dec(v_declName_3480_);
return v___x_3489_;
}
}
else
{
lean_dec(v_a_3486_);
lean_dec_ref(v_body_3483_);
lean_dec_ref(v_value_3482_);
lean_dec_ref(v_type_3481_);
lean_dec_ref_known(v_e_3343_, 4);
lean_dec(v_declName_3480_);
return v___x_3487_;
}
}
else
{
lean_dec_ref(v_body_3483_);
lean_dec_ref(v_value_3482_);
lean_dec_ref(v_type_3481_);
lean_dec_ref_known(v_e_3343_, 4);
lean_dec(v_declName_3480_);
return v___x_3485_;
}
}
default: 
{
lean_object* v___x_3575_; lean_object* v___x_3576_; 
lean_dec_ref(v_e_3343_);
v___x_3575_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1);
v___x_3576_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(v___x_3575_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
return v___x_3576_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(lean_object* v_e_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_){
_start:
{
lean_object* v___x_3586_; lean_object* v_visitedClosed_3587_; lean_object* v___x_3588_; 
v___x_3586_ = lean_st_ref_get(v_a_3578_);
v_visitedClosed_3587_ = lean_ctor_get(v___x_3586_, 3);
lean_inc_ref(v_visitedClosed_3587_);
lean_dec(v___x_3586_);
v___x_3588_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_visitedClosed_3587_, v_e_3577_);
lean_dec_ref(v_visitedClosed_3587_);
if (lean_obj_tag(v___x_3588_) == 1)
{
lean_object* v_val_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3596_; 
lean_dec_ref(v_e_3577_);
v_val_3589_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3591_ = v___x_3588_;
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_val_3589_);
lean_dec(v___x_3588_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3594_; 
if (v_isShared_3592_ == 0)
{
lean_ctor_set_tag(v___x_3591_, 0);
v___x_3594_ = v___x_3591_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_val_3589_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
else
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v_visited_3599_; lean_object* v_types_3600_; lean_object* v_subst_3601_; lean_object* v_visitedClosed_3602_; lean_object* v_hasDepLetCache_3603_; lean_object* v_numConverted_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3674_; 
lean_dec(v___x_3588_);
v___x_3597_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2);
v___x_3598_ = lean_st_ref_take(v_a_3578_);
v_visited_3599_ = lean_ctor_get(v___x_3598_, 0);
v_types_3600_ = lean_ctor_get(v___x_3598_, 1);
v_subst_3601_ = lean_ctor_get(v___x_3598_, 2);
v_visitedClosed_3602_ = lean_ctor_get(v___x_3598_, 3);
v_hasDepLetCache_3603_ = lean_ctor_get(v___x_3598_, 4);
v_numConverted_3604_ = lean_ctor_get(v___x_3598_, 5);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3606_ = v___x_3598_;
v_isShared_3607_ = v_isSharedCheck_3674_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_numConverted_3604_);
lean_inc(v_hasDepLetCache_3603_);
lean_inc(v_visitedClosed_3602_);
lean_inc(v_subst_3601_);
lean_inc(v_types_3600_);
lean_inc(v_visited_3599_);
lean_dec(v___x_3598_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3674_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3608_; lean_object* v___x_3610_; 
v___x_3608_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1);
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 2, v___x_3608_);
lean_ctor_set(v___x_3606_, 1, v___x_3608_);
lean_ctor_set(v___x_3606_, 0, v___x_3608_);
v___x_3610_ = v___x_3606_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3608_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v___x_3608_);
lean_ctor_set(v_reuseFailAlloc_3673_, 2, v___x_3608_);
lean_ctor_set(v_reuseFailAlloc_3673_, 3, v_visitedClosed_3602_);
lean_ctor_set(v_reuseFailAlloc_3673_, 4, v_hasDepLetCache_3603_);
lean_ctor_set(v_reuseFailAlloc_3673_, 5, v_numConverted_3604_);
v___x_3610_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3611_; lean_object* v_r_3612_; 
v___x_3611_ = lean_st_ref_put(v_a_3578_, v___x_3610_);
lean_inc_ref(v_e_3577_);
v_r_3612_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(v_e_3577_, v___x_3597_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
if (lean_obj_tag(v_r_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3653_; 
v_a_3613_ = lean_ctor_get(v_r_3612_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v_r_3612_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3615_ = v_r_3612_;
v_isShared_3616_ = v_isSharedCheck_3653_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v_r_3612_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3653_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
lean_inc(v_a_3613_);
if (v_isShared_3616_ == 0)
{
lean_ctor_set_tag(v___x_3615_, 1);
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3613_);
v___x_3618_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
lean_object* v___x_3619_; 
v___x_3619_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(v_a_3578_, v_visited_3599_, v_types_3600_, v_subst_3601_, v___x_3618_);
lean_dec_ref(v___x_3618_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3642_; 
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3642_ == 0)
{
lean_object* v_unused_3643_; 
v_unused_3643_ = lean_ctor_get(v___x_3619_, 0);
lean_dec(v_unused_3643_);
v___x_3621_ = v___x_3619_;
v_isShared_3622_ = v_isSharedCheck_3642_;
goto v_resetjp_3620_;
}
else
{
lean_dec(v___x_3619_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3642_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3623_; lean_object* v_visited_3624_; lean_object* v_types_3625_; lean_object* v_subst_3626_; lean_object* v_visitedClosed_3627_; lean_object* v_hasDepLetCache_3628_; lean_object* v_numConverted_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3641_; 
v___x_3623_ = lean_st_ref_take(v_a_3578_);
v_visited_3624_ = lean_ctor_get(v___x_3623_, 0);
v_types_3625_ = lean_ctor_get(v___x_3623_, 1);
v_subst_3626_ = lean_ctor_get(v___x_3623_, 2);
v_visitedClosed_3627_ = lean_ctor_get(v___x_3623_, 3);
v_hasDepLetCache_3628_ = lean_ctor_get(v___x_3623_, 4);
v_numConverted_3629_ = lean_ctor_get(v___x_3623_, 5);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3631_ = v___x_3623_;
v_isShared_3632_ = v_isSharedCheck_3641_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_numConverted_3629_);
lean_inc(v_hasDepLetCache_3628_);
lean_inc(v_visitedClosed_3627_);
lean_inc(v_subst_3626_);
lean_inc(v_types_3625_);
lean_inc(v_visited_3624_);
lean_dec(v___x_3623_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3641_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3633_; lean_object* v___x_3635_; 
lean_inc(v_a_3613_);
v___x_3633_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_visitedClosed_3627_, v_e_3577_, v_a_3613_);
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 3, v___x_3633_);
v___x_3635_ = v___x_3631_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_visited_3624_);
lean_ctor_set(v_reuseFailAlloc_3640_, 1, v_types_3625_);
lean_ctor_set(v_reuseFailAlloc_3640_, 2, v_subst_3626_);
lean_ctor_set(v_reuseFailAlloc_3640_, 3, v___x_3633_);
lean_ctor_set(v_reuseFailAlloc_3640_, 4, v_hasDepLetCache_3628_);
lean_ctor_set(v_reuseFailAlloc_3640_, 5, v_numConverted_3629_);
v___x_3635_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
lean_object* v___x_3636_; lean_object* v___x_3638_; 
v___x_3636_ = lean_st_ref_put(v_a_3578_, v___x_3635_);
if (v_isShared_3622_ == 0)
{
lean_ctor_set(v___x_3621_, 0, v_a_3613_);
v___x_3638_ = v___x_3621_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3613_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
}
else
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
lean_dec(v_a_3613_);
lean_dec_ref(v_e_3577_);
v_a_3644_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3619_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3619_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
}
}
else
{
lean_object* v_a_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
lean_dec_ref(v_e_3577_);
v_a_3654_ = lean_ctor_get(v_r_3612_, 0);
lean_inc(v_a_3654_);
lean_dec_ref_known(v_r_3612_, 1);
v___x_3655_ = lean_box(0);
v___x_3656_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(v_a_3578_, v_visited_3599_, v_types_3600_, v_subst_3601_, v___x_3655_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3663_ == 0)
{
lean_object* v_unused_3664_; 
v_unused_3664_ = lean_ctor_get(v___x_3656_, 0);
lean_dec(v_unused_3664_);
v___x_3658_ = v___x_3656_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_dec(v___x_3656_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
lean_ctor_set_tag(v___x_3658_, 1);
lean_ctor_set(v___x_3658_, 0, v_a_3654_);
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3654_);
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
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
lean_dec(v_a_3654_);
v_a_3665_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___x_3656_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3656_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(lean_object* v_e_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_){
_start:
{
lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; 
switch(lean_obj_tag(v_e_3675_))
{
case 0:
{
lean_object* v___x_3751_; 
v___x_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3751_, 0, v_e_3675_);
return v___x_3751_;
}
case 1:
{
lean_object* v___x_3752_; 
v___x_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3752_, 0, v_e_3675_);
return v___x_3752_;
}
case 2:
{
lean_object* v___x_3753_; 
v___x_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3753_, 0, v_e_3675_);
return v___x_3753_;
}
case 3:
{
lean_object* v___x_3754_; 
v___x_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3754_, 0, v_e_3675_);
return v___x_3754_;
}
case 4:
{
lean_object* v___x_3755_; 
v___x_3755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3755_, 0, v_e_3675_);
return v___x_3755_;
}
case 9:
{
lean_object* v___x_3756_; 
v___x_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3756_, 0, v_e_3675_);
return v___x_3756_;
}
default: 
{
lean_object* v_numCandidates_3757_; lean_object* v_cleanSuffix_3758_; lean_object* v___x_3759_; uint8_t v___x_3760_; 
v_numCandidates_3757_ = lean_ctor_get(v_a_3676_, 1);
v_cleanSuffix_3758_ = lean_ctor_get(v_a_3676_, 2);
v___x_3759_ = lean_unsigned_to_nat(0u);
v___x_3760_ = lean_nat_dec_eq(v_numCandidates_3757_, v___x_3759_);
if (v___x_3760_ == 0)
{
lean_object* v___x_3761_; uint8_t v___x_3762_; 
v___x_3761_ = l_Lean_Expr_looseBVarRange(v_e_3675_);
v___x_3762_ = lean_nat_dec_le(v___x_3761_, v_cleanSuffix_3758_);
lean_dec(v___x_3761_);
if (v___x_3762_ == 0)
{
v___y_3686_ = v_a_3676_;
v___y_3687_ = v_a_3677_;
v___y_3688_ = v_a_3678_;
v___y_3689_ = v_a_3679_;
v___y_3690_ = v_a_3680_;
v___y_3691_ = v_a_3681_;
v___y_3692_ = v_a_3682_;
v___y_3693_ = v_a_3683_;
goto v___jp_3685_;
}
else
{
goto v___jp_3732_;
}
}
else
{
goto v___jp_3732_;
}
}
}
v___jp_3685_:
{
uint8_t v___x_3694_; 
v___x_3694_ = l_Lean_Expr_hasLooseBVars(v_e_3675_);
if (v___x_3694_ == 0)
{
lean_object* v___x_3695_; 
v___x_3695_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(v_e_3675_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
return v___x_3695_;
}
else
{
lean_object* v___x_3696_; lean_object* v_visited_3697_; lean_object* v___x_3698_; 
v___x_3696_ = lean_st_ref_get(v___y_3687_);
v_visited_3697_ = lean_ctor_get(v___x_3696_, 0);
lean_inc_ref(v_visited_3697_);
lean_dec(v___x_3696_);
v___x_3698_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_visited_3697_, v_e_3675_);
lean_dec_ref(v_visited_3697_);
if (lean_obj_tag(v___x_3698_) == 1)
{
lean_object* v_val_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
lean_dec_ref(v_e_3675_);
v_val_3699_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3698_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_val_3699_);
lean_dec(v___x_3698_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
lean_ctor_set_tag(v___x_3701_, 0);
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_val_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
else
{
lean_object* v___x_3707_; 
lean_dec(v___x_3698_);
lean_inc_ref(v_e_3675_);
v___x_3707_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(v_e_3675_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3731_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3710_ = v___x_3707_;
v_isShared_3711_ = v_isSharedCheck_3731_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3707_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3731_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3712_; lean_object* v_visited_3713_; lean_object* v_types_3714_; lean_object* v_subst_3715_; lean_object* v_visitedClosed_3716_; lean_object* v_hasDepLetCache_3717_; lean_object* v_numConverted_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3730_; 
v___x_3712_ = lean_st_ref_take(v___y_3687_);
v_visited_3713_ = lean_ctor_get(v___x_3712_, 0);
v_types_3714_ = lean_ctor_get(v___x_3712_, 1);
v_subst_3715_ = lean_ctor_get(v___x_3712_, 2);
v_visitedClosed_3716_ = lean_ctor_get(v___x_3712_, 3);
v_hasDepLetCache_3717_ = lean_ctor_get(v___x_3712_, 4);
v_numConverted_3718_ = lean_ctor_get(v___x_3712_, 5);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3720_ = v___x_3712_;
v_isShared_3721_ = v_isSharedCheck_3730_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_numConverted_3718_);
lean_inc(v_hasDepLetCache_3717_);
lean_inc(v_visitedClosed_3716_);
lean_inc(v_subst_3715_);
lean_inc(v_types_3714_);
lean_inc(v_visited_3713_);
lean_dec(v___x_3712_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3730_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3722_; lean_object* v___x_3724_; 
lean_inc(v_a_3708_);
v___x_3722_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_visited_3713_, v_e_3675_, v_a_3708_);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v___x_3722_);
v___x_3724_ = v___x_3720_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3722_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v_types_3714_);
lean_ctor_set(v_reuseFailAlloc_3729_, 2, v_subst_3715_);
lean_ctor_set(v_reuseFailAlloc_3729_, 3, v_visitedClosed_3716_);
lean_ctor_set(v_reuseFailAlloc_3729_, 4, v_hasDepLetCache_3717_);
lean_ctor_set(v_reuseFailAlloc_3729_, 5, v_numConverted_3718_);
v___x_3724_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
lean_object* v___x_3725_; lean_object* v___x_3727_; 
v___x_3725_ = lean_st_ref_put(v___y_3687_, v___x_3724_);
if (v_isShared_3711_ == 0)
{
v___x_3727_ = v___x_3710_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3708_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3675_);
return v___x_3707_;
}
}
}
}
v___jp_3732_:
{
lean_object* v___x_3733_; 
lean_inc_ref(v_e_3675_);
v___x_3733_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_e_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3742_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3736_ = v___x_3733_;
v_isShared_3737_ = v_isSharedCheck_3742_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3733_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3742_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
uint8_t v___x_3738_; 
v___x_3738_ = lean_unbox(v_a_3734_);
lean_dec(v_a_3734_);
if (v___x_3738_ == 0)
{
lean_object* v___x_3740_; 
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 0, v_e_3675_);
v___x_3740_ = v___x_3736_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_e_3675_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
else
{
lean_del_object(v___x_3736_);
v___y_3686_ = v_a_3676_;
v___y_3687_ = v_a_3677_;
v___y_3688_ = v_a_3678_;
v___y_3689_ = v_a_3679_;
v___y_3690_ = v_a_3680_;
v___y_3691_ = v_a_3681_;
v___y_3692_ = v_a_3682_;
v___y_3693_ = v_a_3683_;
goto v___jp_3685_;
}
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_dec_ref(v_e_3675_);
v_a_3743_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3733_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3733_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0(lean_object* v_body_3763_, lean_object* v_binderType_3764_, lean_object* v_a_3765_, lean_object* v_binderName_3766_, uint8_t v_binderInfo_3767_, lean_object* v_e_3768_, lean_object* v_x_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v___x_3779_; 
lean_inc_ref(v_body_3763_);
v___x_3779_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_body_3763_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3795_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3782_ = v___x_3779_;
v_isShared_3783_ = v_isSharedCheck_3795_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3779_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3795_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
size_t v___x_3784_; size_t v___x_3785_; uint8_t v___x_3786_; 
v___x_3784_ = lean_ptr_addr(v_binderType_3764_);
v___x_3785_ = lean_ptr_addr(v_a_3765_);
v___x_3786_ = lean_usize_dec_eq(v___x_3784_, v___x_3785_);
if (v___x_3786_ == 0)
{
lean_object* v___x_3787_; 
lean_del_object(v___x_3782_);
lean_dec_ref(v_e_3768_);
lean_dec_ref(v_body_3763_);
v___x_3787_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(v_binderName_3766_, v_binderInfo_3767_, v_a_3765_, v_a_3780_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
return v___x_3787_;
}
else
{
size_t v___x_3788_; size_t v___x_3789_; uint8_t v___x_3790_; 
v___x_3788_ = lean_ptr_addr(v_body_3763_);
lean_dec_ref(v_body_3763_);
v___x_3789_ = lean_ptr_addr(v_a_3780_);
v___x_3790_ = lean_usize_dec_eq(v___x_3788_, v___x_3789_);
if (v___x_3790_ == 0)
{
lean_object* v___x_3791_; 
lean_del_object(v___x_3782_);
lean_dec_ref(v_e_3768_);
v___x_3791_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(v_binderName_3766_, v_binderInfo_3767_, v_a_3765_, v_a_3780_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
return v___x_3791_;
}
else
{
lean_object* v___x_3793_; 
lean_dec(v_a_3780_);
lean_dec(v_binderName_3766_);
lean_dec_ref(v_a_3765_);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 0, v_e_3768_);
v___x_3793_ = v___x_3782_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_e_3768_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3768_);
lean_dec(v_binderName_3766_);
lean_dec_ref(v_a_3765_);
lean_dec_ref(v_body_3763_);
return v___x_3779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___boxed(lean_object* v_e_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(v_e_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_);
lean_dec(v_a_3804_);
lean_dec_ref(v_a_3803_);
lean_dec(v_a_3802_);
lean_dec_ref(v_a_3801_);
lean_dec(v_a_3800_);
lean_dec_ref(v_a_3799_);
lean_dec(v_a_3798_);
lean_dec_ref(v_a_3797_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___boxed(lean_object* v_e_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(v_e_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_);
lean_dec(v_a_3814_);
lean_dec_ref(v_a_3813_);
lean_dec(v_a_3812_);
lean_dec_ref(v_a_3811_);
lean_dec(v_a_3810_);
lean_dec_ref(v_a_3809_);
lean_dec(v_a_3808_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit___boxed(lean_object* v_e_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_){
_start:
{
lean_object* v_res_3827_; 
v_res_3827_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_e_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_);
lean_dec(v_a_3825_);
lean_dec_ref(v_a_3824_);
lean_dec(v_a_3823_);
lean_dec_ref(v_a_3822_);
lean_dec(v_a_3821_);
lean_dec_ref(v_a_3820_);
lean_dec(v_a_3819_);
lean_dec_ref(v_a_3818_);
return v_res_3827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___boxed(lean_object* v_e_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(v_e_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
lean_dec(v_a_3836_);
lean_dec_ref(v_a_3835_);
lean_dec(v_a_3834_);
lean_dec_ref(v_a_3833_);
lean_dec(v_a_3832_);
lean_dec_ref(v_a_3831_);
lean_dec(v_a_3830_);
lean_dec_ref(v_a_3829_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1(lean_object* v_f_3839_, lean_object* v_a_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
lean_object* v___x_3850_; 
v___x_3850_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(v_f_3839_, v_a_3840_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
return v___x_3850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___boxed(lean_object* v_f_3851_, lean_object* v_a_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1(v_f_3851_, v_a_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2(lean_object* v_d_3863_, lean_object* v_e_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(v_d_3863_, v_e_3864_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___boxed(lean_object* v_d_3875_, lean_object* v_e_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2(v_d_3875_, v_e_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec_ref(v___y_3879_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3(lean_object* v_structName_3887_, lean_object* v_idx_3888_, lean_object* v_struct_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v___x_3899_; 
v___x_3899_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(v_structName_3887_, v_idx_3888_, v_struct_3889_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
return v___x_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___boxed(lean_object* v_structName_3900_, lean_object* v_idx_3901_, lean_object* v_struct_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3(v_structName_3900_, v_idx_3901_, v_struct_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4(lean_object* v_x_3913_, uint8_t v_bi_3914_, lean_object* v_t_3915_, lean_object* v_b_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v___x_3926_; 
v___x_3926_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(v_x_3913_, v_bi_3914_, v_t_3915_, v_b_3916_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___boxed(lean_object* v_x_3927_, lean_object* v_bi_3928_, lean_object* v_t_3929_, lean_object* v_b_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
uint8_t v_bi_boxed_3940_; lean_object* v_res_3941_; 
v_bi_boxed_3940_ = lean_unbox(v_bi_3928_);
v_res_3941_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4(v_x_3927_, v_bi_boxed_3940_, v_t_3929_, v_b_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
lean_dec(v___y_3934_);
lean_dec_ref(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5(lean_object* v_x_3942_, lean_object* v_t_3943_, lean_object* v_v_3944_, lean_object* v_b_3945_, uint8_t v_nondep_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v___x_3956_; 
v___x_3956_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_x_3942_, v_t_3943_, v_v_3944_, v_b_3945_, v_nondep_3946_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___boxed(lean_object* v_x_3957_, lean_object* v_t_3958_, lean_object* v_v_3959_, lean_object* v_b_3960_, lean_object* v_nondep_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
uint8_t v_nondep_boxed_3971_; lean_object* v_res_3972_; 
v_nondep_boxed_3971_ = lean_unbox(v_nondep_3961_);
v_res_3972_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5(v_x_3957_, v_t_3958_, v_v_3959_, v_b_3960_, v_nondep_boxed_3971_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec_ref(v___y_3964_);
lean_dec(v___y_3963_);
lean_dec_ref(v___y_3962_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8(lean_object* v_x_3973_, uint8_t v_bi_3974_, lean_object* v_t_3975_, lean_object* v_b_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
lean_object* v___x_3986_; 
v___x_3986_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(v_x_3973_, v_bi_3974_, v_t_3975_, v_b_3976_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
return v___x_3986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___boxed(lean_object* v_x_3987_, lean_object* v_bi_3988_, lean_object* v_t_3989_, lean_object* v_b_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_){
_start:
{
uint8_t v_bi_boxed_4000_; lean_object* v_res_4001_; 
v_bi_boxed_4000_ = lean_unbox(v_bi_3988_);
v_res_4001_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8(v_x_3987_, v_bi_boxed_4000_, v_t_3989_, v_b_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed(lean_object* v_e_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_){
_start:
{
lean_object* v___x_4012_; 
v___x_4012_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(v_e_4002_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___boxed(lean_object* v_e_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed(v_e_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_);
lean_dec(v_a_4021_);
lean_dec_ref(v_a_4020_);
lean_dec(v_a_4019_);
lean_dec_ref(v_a_4018_);
lean_dec(v_a_4017_);
lean_dec_ref(v_a_4016_);
lean_dec(v_a_4015_);
lean_dec_ref(v_a_4014_);
return v_res_4023_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6(lean_object* v_00_u03b2_4024_, lean_object* v_k_4025_, lean_object* v_t_4026_){
_start:
{
uint8_t v___x_4027_; 
v___x_4027_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(v_k_4025_, v_t_4026_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___boxed(lean_object* v_00_u03b2_4028_, lean_object* v_k_4029_, lean_object* v_t_4030_){
_start:
{
uint8_t v_res_4031_; lean_object* v_r_4032_; 
v_res_4031_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6(v_00_u03b2_4028_, v_k_4029_, v_t_4030_);
lean_dec(v_t_4030_);
lean_dec(v_k_4029_);
v_r_4032_ = lean_box(v_res_4031_);
return v_r_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0(lean_object* v_x_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v___x_4041_; 
lean_inc(v___y_4035_);
lean_inc_ref(v___y_4034_);
v___x_4041_ = lean_apply_7(v_x_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, lean_box(0));
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0___boxed(lean_object* v_x_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0(v_x_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(lean_object* v_lctx_4051_, lean_object* v_localInsts_4052_, lean_object* v_x_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
lean_object* v___f_4061_; lean_object* v___x_4062_; 
lean_inc(v___y_4055_);
lean_inc_ref(v___y_4054_);
v___f_4061_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4061_, 0, v_x_4053_);
lean_closure_set(v___f_4061_, 1, v___y_4054_);
lean_closure_set(v___f_4061_, 2, v___y_4055_);
v___x_4062_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4051_, v_localInsts_4052_, v___f_4061_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
if (lean_obj_tag(v___x_4062_) == 0)
{
return v___x_4062_;
}
else
{
lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4070_; 
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4065_ = v___x_4062_;
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_a_4063_);
lean_dec(v___x_4062_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4063_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___boxed(lean_object* v_lctx_4071_, lean_object* v_localInsts_4072_, lean_object* v_x_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(v_lctx_4071_, v_localInsts_4072_, v_x_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec_ref(v___y_4074_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0(lean_object* v_00_u03b1_4082_, lean_object* v_lctx_4083_, lean_object* v_localInsts_4084_, lean_object* v_x_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v___x_4093_; 
v___x_4093_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(v_lctx_4083_, v_localInsts_4084_, v_x_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___boxed(lean_object* v_00_u03b1_4094_, lean_object* v_lctx_4095_, lean_object* v_localInsts_4096_, lean_object* v_x_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0(v_00_u03b1_4094_, v_lctx_4095_, v_localInsts_4096_, v_x_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0(lean_object* v_k_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v___x_4114_; 
lean_inc(v___y_4108_);
lean_inc_ref(v___y_4107_);
v___x_4114_ = lean_apply_7(v_k_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, lean_box(0));
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0___boxed(lean_object* v_k_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
lean_object* v_res_4123_; 
v_res_4123_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0(v_k_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg(lean_object* v_k_4124_, uint8_t v_allowLevelAssignments_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v___f_4133_; lean_object* v___x_4134_; 
lean_inc(v___y_4127_);
lean_inc_ref(v___y_4126_);
v___f_4133_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4133_, 0, v_k_4124_);
lean_closure_set(v___f_4133_, 1, v___y_4126_);
lean_closure_set(v___f_4133_, 2, v___y_4127_);
v___x_4134_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_4125_, v___f_4133_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
if (lean_obj_tag(v___x_4134_) == 0)
{
return v___x_4134_;
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4134_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4134_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___boxed(lean_object* v_k_4143_, lean_object* v_allowLevelAssignments_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_4152_; lean_object* v_res_4153_; 
v_allowLevelAssignments_boxed_4152_ = lean_unbox(v_allowLevelAssignments_4144_);
v_res_4153_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg(v_k_4143_, v_allowLevelAssignments_boxed_4152_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
return v_res_4153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1(lean_object* v_00_u03b1_4154_, lean_object* v_k_4155_, uint8_t v_allowLevelAssignments_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_){
_start:
{
lean_object* v___x_4164_; 
v___x_4164_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg(v_k_4155_, v_allowLevelAssignments_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___boxed(lean_object* v_00_u03b1_4165_, lean_object* v_k_4166_, lean_object* v_allowLevelAssignments_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_4175_; lean_object* v_res_4176_; 
v_allowLevelAssignments_boxed_4175_ = lean_unbox(v_allowLevelAssignments_4167_);
v_res_4176_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1(v_00_u03b1_4165_, v_k_4166_, v_allowLevelAssignments_boxed_4175_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec(v___y_4171_);
lean_dec_ref(v___y_4170_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
return v_res_4176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__0(lean_object* v_cfg_4177_){
_start:
{
uint8_t v_foApprox_4178_; uint8_t v_ctxApprox_4179_; uint8_t v_quasiPatternApprox_4180_; uint8_t v_constApprox_4181_; uint8_t v_isDefEqStuckEx_4182_; uint8_t v_unificationHints_4183_; uint8_t v_proofIrrelevance_4184_; uint8_t v_assignSyntheticOpaque_4185_; uint8_t v_offsetCnstrs_4186_; uint8_t v_transparency_4187_; uint8_t v_univApprox_4188_; uint8_t v_zetaUnused_4189_; uint8_t v_canUnfoldPredicateConfig_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4200_; 
v_foApprox_4178_ = lean_ctor_get_uint8(v_cfg_4177_, 0);
v_ctxApprox_4179_ = lean_ctor_get_uint8(v_cfg_4177_, 1);
v_quasiPatternApprox_4180_ = lean_ctor_get_uint8(v_cfg_4177_, 2);
v_constApprox_4181_ = lean_ctor_get_uint8(v_cfg_4177_, 3);
v_isDefEqStuckEx_4182_ = lean_ctor_get_uint8(v_cfg_4177_, 4);
v_unificationHints_4183_ = lean_ctor_get_uint8(v_cfg_4177_, 5);
v_proofIrrelevance_4184_ = lean_ctor_get_uint8(v_cfg_4177_, 6);
v_assignSyntheticOpaque_4185_ = lean_ctor_get_uint8(v_cfg_4177_, 7);
v_offsetCnstrs_4186_ = lean_ctor_get_uint8(v_cfg_4177_, 8);
v_transparency_4187_ = lean_ctor_get_uint8(v_cfg_4177_, 9);
v_univApprox_4188_ = lean_ctor_get_uint8(v_cfg_4177_, 11);
v_zetaUnused_4189_ = lean_ctor_get_uint8(v_cfg_4177_, 17);
v_canUnfoldPredicateConfig_4190_ = lean_ctor_get_uint8(v_cfg_4177_, 19);
v_isSharedCheck_4200_ = !lean_is_exclusive(v_cfg_4177_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4192_ = v_cfg_4177_;
v_isShared_4193_ = v_isSharedCheck_4200_;
goto v_resetjp_4191_;
}
else
{
lean_dec(v_cfg_4177_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4200_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
uint8_t v___x_4194_; uint8_t v___x_4195_; uint8_t v___x_4196_; lean_object* v___x_4198_; 
v___x_4194_ = 0;
v___x_4195_ = 1;
v___x_4196_ = 2;
if (v_isShared_4193_ == 0)
{
v___x_4198_ = v___x_4192_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4199_, 0, v_foApprox_4178_);
lean_ctor_set_uint8(v_reuseFailAlloc_4199_, 1, v_ctxApprox_4179_);
lean_ctor_set_uint8(v_reuseFailAlloc_4199_, 2, v_quasiPatternApprox_4180_);
lean_ctor_set_uint8(v_reuseFailAlloc_4199_, 3, v_constApprox_4181_);
lean_ctor_set_uint8(v_reuseFailAlloc_4199_, 4, v_isDefEqStuckEx_4182_);
lean_ctor_set_uint8(v_reuseFailAlloc_4199_, 5, v_unificationHints_4183_);
lean_ctor_set_uint8(v_reuseFailAlloc_4199_, 6, v_proofIrrelevance_4184_);
lean_ctor_set_uint8(v_reuseFailAlloc_4199_, 7, v_assignSyntheticOpaque_4185_);
lean_ctor_set_uint8(v_reuseFailAlloc_4199_, 8, v_offsetCnstrs_4186_);
lean_ctor_set_uint8(v_reuseFailAlloc_4199_, 9, v_transparency_4187_);
lean_ctor_set_uint8(v_reuseFailAlloc_4199_, 11, v_univApprox_4188_);
lean_ctor_set_uint8(v_reuseFailAlloc_4199_, 17, v_zetaUnused_4189_);
lean_ctor_set_uint8(v_reuseFailAlloc_4199_, 19, v_canUnfoldPredicateConfig_4190_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
lean_ctor_set_uint8(v___x_4198_, 10, v___x_4194_);
lean_ctor_set_uint8(v___x_4198_, 12, v___x_4195_);
lean_ctor_set_uint8(v___x_4198_, 13, v___x_4195_);
lean_ctor_set_uint8(v___x_4198_, 14, v___x_4196_);
lean_ctor_set_uint8(v___x_4198_, 15, v___x_4195_);
lean_ctor_set_uint8(v___x_4198_, 16, v___x_4195_);
lean_ctor_set_uint8(v___x_4198_, 18, v___x_4195_);
return v___x_4198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__1(lean_object* v___x_4201_, lean_object* v_e_4202_, lean_object* v___x_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v___x_4211_; lean_object* v_a_4213_; lean_object* v___x_4216_; 
v___x_4211_ = lean_st_mk_ref(v___x_4201_);
lean_inc_ref(v_e_4202_);
v___x_4216_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_e_4202_, v___x_4203_, v___x_4211_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; uint8_t v___x_4218_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
lean_inc(v_a_4217_);
lean_dec_ref_known(v___x_4216_, 1);
v___x_4218_ = lean_unbox(v_a_4217_);
lean_dec(v_a_4217_);
if (v___x_4218_ == 0)
{
v_a_4213_ = v_e_4202_;
goto v___jp_4212_;
}
else
{
lean_object* v___x_4219_; 
v___x_4219_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_e_4202_, v___x_4203_, v___x_4211_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_object* v_a_4220_; 
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
lean_inc(v_a_4220_);
lean_dec_ref_known(v___x_4219_, 1);
v_a_4213_ = v_a_4220_;
goto v___jp_4212_;
}
else
{
lean_dec(v___x_4211_);
return v___x_4219_;
}
}
}
else
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4228_; 
lean_dec(v___x_4211_);
lean_dec_ref(v_e_4202_);
v_a_4221_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4223_ = v___x_4216_;
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4216_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4226_; 
if (v_isShared_4224_ == 0)
{
v___x_4226_ = v___x_4223_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
v___jp_4212_:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4214_ = lean_st_ref_get(v___x_4211_);
lean_dec(v___x_4211_);
lean_dec(v___x_4214_);
v___x_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4215_, 0, v_a_4213_);
return v___x_4215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__1___boxed(lean_object* v___x_4229_, lean_object* v_e_4230_, lean_object* v___x_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
lean_object* v_res_4239_; 
v_res_4239_ = l_Lean_Meta_Sym_letToHave___lam__1(v___x_4229_, v_e_4230_, v___x_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec_ref(v___x_4231_);
return v_res_4239_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___lam__2___closed__0(void){
_start:
{
lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4240_ = lean_unsigned_to_nat(0u);
v___x_4241_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1);
v___x_4242_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4241_);
lean_ctor_set(v___x_4242_, 1, v___x_4241_);
lean_ctor_set(v___x_4242_, 2, v___x_4241_);
lean_ctor_set(v___x_4242_, 3, v___x_4241_);
lean_ctor_set(v___x_4242_, 4, v___x_4241_);
lean_ctor_set(v___x_4242_, 5, v___x_4240_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__2(lean_object* v_e_4243_, lean_object* v_____do__lift_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_){
_start:
{
lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___f_4255_; lean_object* v___x_4256_; 
v___x_4252_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___closed__0));
v___x_4253_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2);
v___x_4254_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__2___closed__0, &l_Lean_Meta_Sym_letToHave___lam__2___closed__0_once, _init_l_Lean_Meta_Sym_letToHave___lam__2___closed__0);
v___f_4255_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_letToHave___lam__1___boxed), 10, 3);
lean_closure_set(v___f_4255_, 0, v___x_4254_);
lean_closure_set(v___f_4255_, 1, v_e_4243_);
lean_closure_set(v___f_4255_, 2, v___x_4253_);
v___x_4256_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(v_____do__lift_4244_, v___x_4252_, v___f_4255_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
return v___x_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__2___boxed(lean_object* v_e_4257_, lean_object* v_____do__lift_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Lean_Meta_Sym_letToHave___lam__2(v_e_4257_, v_____do__lift_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__3(lean_object* v___y_4267_, lean_object* v_zetaDeltaFVarIds_4268_, lean_object* v_a_x3f_4269_){
_start:
{
lean_object* v___x_4271_; lean_object* v_mctx_4272_; lean_object* v_cache_4273_; lean_object* v_postponed_4274_; lean_object* v_diag_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4285_; 
v___x_4271_ = lean_st_ref_take(v___y_4267_);
v_mctx_4272_ = lean_ctor_get(v___x_4271_, 0);
v_cache_4273_ = lean_ctor_get(v___x_4271_, 1);
v_postponed_4274_ = lean_ctor_get(v___x_4271_, 3);
v_diag_4275_ = lean_ctor_get(v___x_4271_, 4);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4271_);
if (v_isSharedCheck_4285_ == 0)
{
lean_object* v_unused_4286_; 
v_unused_4286_ = lean_ctor_get(v___x_4271_, 2);
lean_dec(v_unused_4286_);
v___x_4277_ = v___x_4271_;
v_isShared_4278_ = v_isSharedCheck_4285_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_diag_4275_);
lean_inc(v_postponed_4274_);
lean_inc(v_cache_4273_);
lean_inc(v_mctx_4272_);
lean_dec(v___x_4271_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4285_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4280_; 
if (v_isShared_4278_ == 0)
{
lean_ctor_set(v___x_4277_, 2, v_zetaDeltaFVarIds_4268_);
v___x_4280_ = v___x_4277_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_mctx_4272_);
lean_ctor_set(v_reuseFailAlloc_4284_, 1, v_cache_4273_);
lean_ctor_set(v_reuseFailAlloc_4284_, 2, v_zetaDeltaFVarIds_4268_);
lean_ctor_set(v_reuseFailAlloc_4284_, 3, v_postponed_4274_);
lean_ctor_set(v_reuseFailAlloc_4284_, 4, v_diag_4275_);
v___x_4280_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; 
v___x_4281_ = lean_st_ref_put(v___y_4267_, v___x_4280_);
v___x_4282_ = lean_box(0);
v___x_4283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4283_, 0, v___x_4282_);
return v___x_4283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__3___boxed(lean_object* v___y_4287_, lean_object* v_zetaDeltaFVarIds_4288_, lean_object* v_a_x3f_4289_, lean_object* v___y_4290_){
_start:
{
lean_object* v_res_4291_; 
v_res_4291_ = l_Lean_Meta_Sym_letToHave___lam__3(v___y_4287_, v_zetaDeltaFVarIds_4288_, v_a_x3f_4289_);
lean_dec(v_a_x3f_4289_);
lean_dec(v___y_4287_);
return v_res_4291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__4(lean_object* v___y_4292_, lean_object* v_cache_4293_, lean_object* v_a_x3f_4294_){
_start:
{
lean_object* v___x_4296_; lean_object* v_mctx_4297_; lean_object* v_zetaDeltaFVarIds_4298_; lean_object* v_postponed_4299_; lean_object* v_diag_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4310_; 
v___x_4296_ = lean_st_ref_take(v___y_4292_);
v_mctx_4297_ = lean_ctor_get(v___x_4296_, 0);
v_zetaDeltaFVarIds_4298_ = lean_ctor_get(v___x_4296_, 2);
v_postponed_4299_ = lean_ctor_get(v___x_4296_, 3);
v_diag_4300_ = lean_ctor_get(v___x_4296_, 4);
v_isSharedCheck_4310_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4310_ == 0)
{
lean_object* v_unused_4311_; 
v_unused_4311_ = lean_ctor_get(v___x_4296_, 1);
lean_dec(v_unused_4311_);
v___x_4302_ = v___x_4296_;
v_isShared_4303_ = v_isSharedCheck_4310_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_diag_4300_);
lean_inc(v_postponed_4299_);
lean_inc(v_zetaDeltaFVarIds_4298_);
lean_inc(v_mctx_4297_);
lean_dec(v___x_4296_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4310_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
lean_ctor_set(v___x_4302_, 1, v_cache_4293_);
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_mctx_4297_);
lean_ctor_set(v_reuseFailAlloc_4309_, 1, v_cache_4293_);
lean_ctor_set(v_reuseFailAlloc_4309_, 2, v_zetaDeltaFVarIds_4298_);
lean_ctor_set(v_reuseFailAlloc_4309_, 3, v_postponed_4299_);
lean_ctor_set(v_reuseFailAlloc_4309_, 4, v_diag_4300_);
v___x_4305_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; 
v___x_4306_ = lean_st_ref_put(v___y_4292_, v___x_4305_);
v___x_4307_ = lean_box(0);
v___x_4308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4307_);
return v___x_4308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__4___boxed(lean_object* v___y_4312_, lean_object* v_cache_4313_, lean_object* v_a_x3f_4314_, lean_object* v___y_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = l_Lean_Meta_Sym_letToHave___lam__4(v___y_4312_, v_cache_4313_, v_a_x3f_4314_);
lean_dec(v_a_x3f_4314_);
lean_dec(v___y_4312_);
return v_res_4316_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__0(void){
_start:
{
lean_object* v___x_4317_; 
v___x_4317_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4317_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__1(void){
_start:
{
lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4318_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__5___closed__0, &l_Lean_Meta_Sym_letToHave___lam__5___closed__0_once, _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__0);
v___x_4319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4318_);
return v___x_4319_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__2(void){
_start:
{
lean_object* v___x_4320_; lean_object* v___x_4321_; 
v___x_4320_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__5___closed__1, &l_Lean_Meta_Sym_letToHave___lam__5___closed__1_once, _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__1);
v___x_4321_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4320_);
lean_ctor_set(v___x_4321_, 1, v___x_4320_);
lean_ctor_set(v___x_4321_, 2, v___x_4320_);
lean_ctor_set(v___x_4321_, 3, v___x_4320_);
lean_ctor_set(v___x_4321_, 4, v___x_4320_);
lean_ctor_set(v___x_4321_, 5, v___x_4320_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__5(uint8_t v___x_4322_, lean_object* v___f_4323_, lean_object* v___f_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_){
_start:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v_mctx_4334_; lean_object* v_zetaDeltaFVarIds_4335_; lean_object* v_postponed_4336_; lean_object* v_diag_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4423_; 
v___x_4332_ = lean_st_ref_get(v___y_4328_);
v___x_4333_ = lean_st_ref_take(v___y_4328_);
v_mctx_4334_ = lean_ctor_get(v___x_4333_, 0);
v_zetaDeltaFVarIds_4335_ = lean_ctor_get(v___x_4333_, 2);
v_postponed_4336_ = lean_ctor_get(v___x_4333_, 3);
v_diag_4337_ = lean_ctor_get(v___x_4333_, 4);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4423_ == 0)
{
lean_object* v_unused_4424_; 
v_unused_4424_ = lean_ctor_get(v___x_4333_, 1);
lean_dec(v_unused_4424_);
v___x_4339_ = v___x_4333_;
v_isShared_4340_ = v_isSharedCheck_4423_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_diag_4337_);
lean_inc(v_postponed_4336_);
lean_inc(v_zetaDeltaFVarIds_4335_);
lean_inc(v_mctx_4334_);
lean_dec(v___x_4333_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4423_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4341_; lean_object* v___x_4343_; 
v___x_4341_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__5___closed__2, &l_Lean_Meta_Sym_letToHave___lam__5___closed__2_once, _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__2);
if (v_isShared_4340_ == 0)
{
lean_ctor_set(v___x_4339_, 1, v___x_4341_);
v___x_4343_ = v___x_4339_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_mctx_4334_);
lean_ctor_set(v_reuseFailAlloc_4422_, 1, v___x_4341_);
lean_ctor_set(v_reuseFailAlloc_4422_, 2, v_zetaDeltaFVarIds_4335_);
lean_ctor_set(v_reuseFailAlloc_4422_, 3, v_postponed_4336_);
lean_ctor_set(v_reuseFailAlloc_4422_, 4, v_diag_4337_);
v___x_4343_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v_mctx_4346_; lean_object* v_cache_4347_; lean_object* v_zetaDeltaFVarIds_4348_; lean_object* v_postponed_4349_; lean_object* v_diag_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4421_; 
v___x_4344_ = lean_st_ref_put(v___y_4328_, v___x_4343_);
v___x_4345_ = lean_st_ref_take(v___y_4328_);
v_mctx_4346_ = lean_ctor_get(v___x_4345_, 0);
v_cache_4347_ = lean_ctor_get(v___x_4345_, 1);
v_zetaDeltaFVarIds_4348_ = lean_ctor_get(v___x_4345_, 2);
v_postponed_4349_ = lean_ctor_get(v___x_4345_, 3);
v_diag_4350_ = lean_ctor_get(v___x_4345_, 4);
v_isSharedCheck_4421_ = !lean_is_exclusive(v___x_4345_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4352_ = v___x_4345_;
v_isShared_4353_ = v_isSharedCheck_4421_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_diag_4350_);
lean_inc(v_postponed_4349_);
lean_inc(v_zetaDeltaFVarIds_4348_);
lean_inc(v_cache_4347_);
lean_inc(v_mctx_4346_);
lean_dec(v___x_4345_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4421_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4354_; lean_object* v___x_4356_; 
v___x_4354_ = lean_box(1);
if (v_isShared_4353_ == 0)
{
lean_ctor_set(v___x_4352_, 2, v___x_4354_);
v___x_4356_ = v___x_4352_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_mctx_4346_);
lean_ctor_set(v_reuseFailAlloc_4420_, 1, v_cache_4347_);
lean_ctor_set(v_reuseFailAlloc_4420_, 2, v___x_4354_);
lean_ctor_set(v_reuseFailAlloc_4420_, 3, v_postponed_4349_);
lean_ctor_set(v_reuseFailAlloc_4420_, 4, v_diag_4350_);
v___x_4356_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
lean_object* v___x_4357_; lean_object* v_cache_4358_; lean_object* v_keyedConfig_4359_; lean_object* v_zetaDeltaSet_4360_; lean_object* v_lctx_4361_; lean_object* v_localInstances_4362_; lean_object* v_defEqCtx_x3f_4363_; lean_object* v_synthPendingDepth_4364_; lean_object* v_customCanUnfoldPredicate_x3f_4365_; uint8_t v_univApprox_4366_; uint8_t v_inTypeClassResolution_4367_; uint8_t v_cacheInferType_4368_; uint8_t v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; uint8_t v_transparency_4372_; lean_object* v_a_4374_; lean_object* v_a_4386_; lean_object* v_a_4399_; uint8_t v___x_4402_; 
v___x_4357_ = lean_st_ref_put(v___y_4328_, v___x_4356_);
v_cache_4358_ = lean_ctor_get(v___x_4332_, 1);
lean_inc_ref(v_cache_4358_);
lean_dec(v___x_4332_);
v_keyedConfig_4359_ = lean_ctor_get(v___y_4327_, 0);
v_zetaDeltaSet_4360_ = lean_ctor_get(v___y_4327_, 1);
v_lctx_4361_ = lean_ctor_get(v___y_4327_, 2);
v_localInstances_4362_ = lean_ctor_get(v___y_4327_, 3);
v_defEqCtx_x3f_4363_ = lean_ctor_get(v___y_4327_, 4);
v_synthPendingDepth_4364_ = lean_ctor_get(v___y_4327_, 5);
v_customCanUnfoldPredicate_x3f_4365_ = lean_ctor_get(v___y_4327_, 6);
v_univApprox_4366_ = lean_ctor_get_uint8(v___y_4327_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4367_ = lean_ctor_get_uint8(v___y_4327_, sizeof(void*)*7 + 2);
v_cacheInferType_4368_ = lean_ctor_get_uint8(v___y_4327_, sizeof(void*)*7 + 3);
v___x_4369_ = 1;
lean_inc(v_customCanUnfoldPredicate_x3f_4365_);
lean_inc(v_synthPendingDepth_4364_);
lean_inc(v_defEqCtx_x3f_4363_);
lean_inc_ref(v_localInstances_4362_);
lean_inc_ref(v_lctx_4361_);
lean_inc(v_zetaDeltaSet_4360_);
lean_inc_ref(v_keyedConfig_4359_);
v___x_4370_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4370_, 0, v_keyedConfig_4359_);
lean_ctor_set(v___x_4370_, 1, v_zetaDeltaSet_4360_);
lean_ctor_set(v___x_4370_, 2, v_lctx_4361_);
lean_ctor_set(v___x_4370_, 3, v_localInstances_4362_);
lean_ctor_set(v___x_4370_, 4, v_defEqCtx_x3f_4363_);
lean_ctor_set(v___x_4370_, 5, v_synthPendingDepth_4364_);
lean_ctor_set(v___x_4370_, 6, v_customCanUnfoldPredicate_x3f_4365_);
lean_ctor_set_uint8(v___x_4370_, sizeof(void*)*7, v___x_4369_);
lean_ctor_set_uint8(v___x_4370_, sizeof(void*)*7 + 1, v_univApprox_4366_);
lean_ctor_set_uint8(v___x_4370_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4367_);
lean_ctor_set_uint8(v___x_4370_, sizeof(void*)*7 + 3, v_cacheInferType_4368_);
v___x_4371_ = l_Lean_Meta_Context_config(v___x_4370_);
lean_dec_ref_known(v___x_4370_, 7);
v_transparency_4372_ = lean_ctor_get_uint8(v___x_4371_, 9);
v___x_4402_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4372_, v___x_4322_);
if (v___x_4402_ == 0)
{
lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; uint64_t v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; 
lean_dec_ref(v___x_4371_);
lean_inc_ref(v_keyedConfig_4359_);
v___x_4403_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4322_, v_keyedConfig_4359_);
lean_inc_n(v_customCanUnfoldPredicate_x3f_4365_, 2);
lean_inc_n(v_synthPendingDepth_4364_, 2);
lean_inc_n(v_defEqCtx_x3f_4363_, 2);
lean_inc_ref_n(v_localInstances_4362_, 2);
lean_inc_ref_n(v_lctx_4361_, 3);
lean_inc_n(v_zetaDeltaSet_4360_, 2);
v___x_4404_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4404_, 0, v___x_4403_);
lean_ctor_set(v___x_4404_, 1, v_zetaDeltaSet_4360_);
lean_ctor_set(v___x_4404_, 2, v_lctx_4361_);
lean_ctor_set(v___x_4404_, 3, v_localInstances_4362_);
lean_ctor_set(v___x_4404_, 4, v_defEqCtx_x3f_4363_);
lean_ctor_set(v___x_4404_, 5, v_synthPendingDepth_4364_);
lean_ctor_set(v___x_4404_, 6, v_customCanUnfoldPredicate_x3f_4365_);
lean_ctor_set_uint8(v___x_4404_, sizeof(void*)*7, v___x_4369_);
lean_ctor_set_uint8(v___x_4404_, sizeof(void*)*7 + 1, v_univApprox_4366_);
lean_ctor_set_uint8(v___x_4404_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4367_);
lean_ctor_set_uint8(v___x_4404_, sizeof(void*)*7 + 3, v_cacheInferType_4368_);
v___x_4405_ = l_Lean_Meta_Context_config(v___x_4404_);
lean_dec_ref_known(v___x_4404_, 7);
v___x_4406_ = lean_apply_1(v___f_4323_, v___x_4405_);
v___x_4407_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4406_);
v___x_4408_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4408_, 0, v___x_4406_);
lean_ctor_set_uint64(v___x_4408_, sizeof(void*)*1, v___x_4407_);
v___x_4409_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4409_, 0, v___x_4408_);
lean_ctor_set(v___x_4409_, 1, v_zetaDeltaSet_4360_);
lean_ctor_set(v___x_4409_, 2, v_lctx_4361_);
lean_ctor_set(v___x_4409_, 3, v_localInstances_4362_);
lean_ctor_set(v___x_4409_, 4, v_defEqCtx_x3f_4363_);
lean_ctor_set(v___x_4409_, 5, v_synthPendingDepth_4364_);
lean_ctor_set(v___x_4409_, 6, v_customCanUnfoldPredicate_x3f_4365_);
lean_ctor_set_uint8(v___x_4409_, sizeof(void*)*7, v___x_4369_);
lean_ctor_set_uint8(v___x_4409_, sizeof(void*)*7 + 1, v_univApprox_4366_);
lean_ctor_set_uint8(v___x_4409_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4367_);
lean_ctor_set_uint8(v___x_4409_, sizeof(void*)*7 + 3, v_cacheInferType_4368_);
lean_inc(v___y_4330_);
lean_inc_ref(v___y_4329_);
lean_inc(v___y_4328_);
lean_inc(v___y_4326_);
lean_inc_ref(v___y_4325_);
v___x_4410_ = lean_apply_8(v___f_4324_, v_lctx_4361_, v___y_4325_, v___y_4326_, v___x_4409_, v___y_4328_, v___y_4329_, v___y_4330_, lean_box(0));
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref_known(v___x_4410_, 1);
v_a_4386_ = v_a_4411_;
goto v___jp_4385_;
}
else
{
lean_object* v_a_4412_; 
v_a_4412_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4412_);
lean_dec_ref_known(v___x_4410_, 1);
v_a_4399_ = v_a_4412_;
goto v___jp_4398_;
}
}
else
{
lean_object* v___x_4413_; uint64_t v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; 
v___x_4413_ = lean_apply_1(v___f_4323_, v___x_4371_);
v___x_4414_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4413_);
v___x_4415_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4415_, 0, v___x_4413_);
lean_ctor_set_uint64(v___x_4415_, sizeof(void*)*1, v___x_4414_);
lean_inc(v_customCanUnfoldPredicate_x3f_4365_);
lean_inc(v_synthPendingDepth_4364_);
lean_inc(v_defEqCtx_x3f_4363_);
lean_inc_ref(v_localInstances_4362_);
lean_inc_ref_n(v_lctx_4361_, 2);
lean_inc(v_zetaDeltaSet_4360_);
v___x_4416_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4416_, 0, v___x_4415_);
lean_ctor_set(v___x_4416_, 1, v_zetaDeltaSet_4360_);
lean_ctor_set(v___x_4416_, 2, v_lctx_4361_);
lean_ctor_set(v___x_4416_, 3, v_localInstances_4362_);
lean_ctor_set(v___x_4416_, 4, v_defEqCtx_x3f_4363_);
lean_ctor_set(v___x_4416_, 5, v_synthPendingDepth_4364_);
lean_ctor_set(v___x_4416_, 6, v_customCanUnfoldPredicate_x3f_4365_);
lean_ctor_set_uint8(v___x_4416_, sizeof(void*)*7, v___x_4369_);
lean_ctor_set_uint8(v___x_4416_, sizeof(void*)*7 + 1, v_univApprox_4366_);
lean_ctor_set_uint8(v___x_4416_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4367_);
lean_ctor_set_uint8(v___x_4416_, sizeof(void*)*7 + 3, v_cacheInferType_4368_);
lean_inc(v___y_4330_);
lean_inc_ref(v___y_4329_);
lean_inc(v___y_4328_);
lean_inc(v___y_4326_);
lean_inc_ref(v___y_4325_);
v___x_4417_ = lean_apply_8(v___f_4324_, v_lctx_4361_, v___y_4325_, v___y_4326_, v___x_4416_, v___y_4328_, v___y_4329_, v___y_4330_, lean_box(0));
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v_a_4418_; 
v_a_4418_ = lean_ctor_get(v___x_4417_, 0);
lean_inc(v_a_4418_);
lean_dec_ref_known(v___x_4417_, 1);
v_a_4386_ = v_a_4418_;
goto v___jp_4385_;
}
else
{
lean_object* v_a_4419_; 
v_a_4419_ = lean_ctor_get(v___x_4417_, 0);
lean_inc(v_a_4419_);
lean_dec_ref_known(v___x_4417_, 1);
v_a_4399_ = v_a_4419_;
goto v___jp_4398_;
}
}
v___jp_4373_:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4383_; 
v___x_4375_ = lean_box(0);
v___x_4376_ = l_Lean_Meta_Sym_letToHave___lam__4(v___y_4328_, v_cache_4358_, v___x_4375_);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4376_);
if (v_isSharedCheck_4383_ == 0)
{
lean_object* v_unused_4384_; 
v_unused_4384_ = lean_ctor_get(v___x_4376_, 0);
lean_dec(v_unused_4384_);
v___x_4378_ = v___x_4376_;
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
else
{
lean_dec(v___x_4376_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4381_; 
if (v_isShared_4379_ == 0)
{
lean_ctor_set_tag(v___x_4378_, 1);
lean_ctor_set(v___x_4378_, 0, v_a_4374_);
v___x_4381_ = v___x_4378_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_a_4374_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
v___jp_4385_:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
lean_inc(v_a_4386_);
v___x_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4387_, 0, v_a_4386_);
v___x_4388_ = l_Lean_Meta_Sym_letToHave___lam__3(v___y_4328_, v_zetaDeltaFVarIds_4348_, v___x_4387_);
lean_dec_ref(v___x_4388_);
v___x_4389_ = l_Lean_Meta_Sym_letToHave___lam__4(v___y_4328_, v_cache_4358_, v___x_4387_);
lean_dec_ref_known(v___x_4387_, 1);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4389_);
if (v_isSharedCheck_4396_ == 0)
{
lean_object* v_unused_4397_; 
v_unused_4397_ = lean_ctor_get(v___x_4389_, 0);
lean_dec(v_unused_4397_);
v___x_4391_ = v___x_4389_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_dec(v___x_4389_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
lean_ctor_set(v___x_4391_, 0, v_a_4386_);
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4386_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
v___jp_4398_:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4400_ = lean_box(0);
v___x_4401_ = l_Lean_Meta_Sym_letToHave___lam__3(v___y_4328_, v_zetaDeltaFVarIds_4348_, v___x_4400_);
lean_dec_ref(v___x_4401_);
v_a_4374_ = v_a_4399_;
goto v___jp_4373_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__5___boxed(lean_object* v___x_4425_, lean_object* v___f_4426_, lean_object* v___f_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_){
_start:
{
uint8_t v___x_18482__boxed_4435_; lean_object* v_res_4436_; 
v___x_18482__boxed_4435_ = lean_unbox(v___x_4425_);
v_res_4436_ = l_Lean_Meta_Sym_letToHave___lam__5(v___x_18482__boxed_4435_, v___f_4426_, v___f_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(lean_object* v_msg_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_){
_start:
{
lean_object* v_ref_4443_; lean_object* v___x_4444_; lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4453_; 
v_ref_4443_ = lean_ctor_get(v___y_4440_, 4);
v___x_4444_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(v_msg_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
v_a_4445_ = lean_ctor_get(v___x_4444_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4447_ = v___x_4444_;
v_isShared_4448_ = v_isSharedCheck_4453_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4444_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4453_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4449_; lean_object* v___x_4451_; 
lean_inc(v_ref_4443_);
v___x_4449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4449_, 0, v_ref_4443_);
lean_ctor_set(v___x_4449_, 1, v_a_4445_);
if (v_isShared_4448_ == 0)
{
lean_ctor_set_tag(v___x_4447_, 1);
lean_ctor_set(v___x_4447_, 0, v___x_4449_);
v___x_4451_ = v___x_4447_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v___x_4449_);
v___x_4451_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
return v___x_4451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg___boxed(lean_object* v_msg_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_){
_start:
{
lean_object* v_res_4460_; 
v_res_4460_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(v_msg_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
lean_dec(v___y_4458_);
lean_dec_ref(v___y_4457_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(lean_object* v___y_4461_, uint8_t v_isExporting_4462_, lean_object* v___x_4463_, lean_object* v___y_4464_, lean_object* v___x_4465_, lean_object* v_a_x3f_4466_){
_start:
{
lean_object* v___x_4468_; lean_object* v_env_4469_; lean_object* v_nextMacroScope_4470_; lean_object* v_ngen_4471_; lean_object* v_auxDeclNGen_4472_; lean_object* v_traceState_4473_; lean_object* v_messages_4474_; lean_object* v_infoState_4475_; lean_object* v_snapshotTasks_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4501_; 
v___x_4468_ = lean_st_ref_take(v___y_4461_);
v_env_4469_ = lean_ctor_get(v___x_4468_, 0);
v_nextMacroScope_4470_ = lean_ctor_get(v___x_4468_, 1);
v_ngen_4471_ = lean_ctor_get(v___x_4468_, 2);
v_auxDeclNGen_4472_ = lean_ctor_get(v___x_4468_, 3);
v_traceState_4473_ = lean_ctor_get(v___x_4468_, 4);
v_messages_4474_ = lean_ctor_get(v___x_4468_, 6);
v_infoState_4475_ = lean_ctor_get(v___x_4468_, 7);
v_snapshotTasks_4476_ = lean_ctor_get(v___x_4468_, 8);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4468_);
if (v_isSharedCheck_4501_ == 0)
{
lean_object* v_unused_4502_; 
v_unused_4502_ = lean_ctor_get(v___x_4468_, 5);
lean_dec(v_unused_4502_);
v___x_4478_ = v___x_4468_;
v_isShared_4479_ = v_isSharedCheck_4501_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_snapshotTasks_4476_);
lean_inc(v_infoState_4475_);
lean_inc(v_messages_4474_);
lean_inc(v_traceState_4473_);
lean_inc(v_auxDeclNGen_4472_);
lean_inc(v_ngen_4471_);
lean_inc(v_nextMacroScope_4470_);
lean_inc(v_env_4469_);
lean_dec(v___x_4468_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4501_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4480_; lean_object* v___x_4482_; 
v___x_4480_ = l_Lean_Environment_setExporting(v_env_4469_, v_isExporting_4462_);
if (v_isShared_4479_ == 0)
{
lean_ctor_set(v___x_4478_, 5, v___x_4463_);
lean_ctor_set(v___x_4478_, 0, v___x_4480_);
v___x_4482_ = v___x_4478_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v___x_4480_);
lean_ctor_set(v_reuseFailAlloc_4500_, 1, v_nextMacroScope_4470_);
lean_ctor_set(v_reuseFailAlloc_4500_, 2, v_ngen_4471_);
lean_ctor_set(v_reuseFailAlloc_4500_, 3, v_auxDeclNGen_4472_);
lean_ctor_set(v_reuseFailAlloc_4500_, 4, v_traceState_4473_);
lean_ctor_set(v_reuseFailAlloc_4500_, 5, v___x_4463_);
lean_ctor_set(v_reuseFailAlloc_4500_, 6, v_messages_4474_);
lean_ctor_set(v_reuseFailAlloc_4500_, 7, v_infoState_4475_);
lean_ctor_set(v_reuseFailAlloc_4500_, 8, v_snapshotTasks_4476_);
v___x_4482_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v_mctx_4485_; lean_object* v_zetaDeltaFVarIds_4486_; lean_object* v_postponed_4487_; lean_object* v_diag_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4498_; 
v___x_4483_ = lean_st_ref_put(v___y_4461_, v___x_4482_);
v___x_4484_ = lean_st_ref_take(v___y_4464_);
v_mctx_4485_ = lean_ctor_get(v___x_4484_, 0);
v_zetaDeltaFVarIds_4486_ = lean_ctor_get(v___x_4484_, 2);
v_postponed_4487_ = lean_ctor_get(v___x_4484_, 3);
v_diag_4488_ = lean_ctor_get(v___x_4484_, 4);
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4498_ == 0)
{
lean_object* v_unused_4499_; 
v_unused_4499_ = lean_ctor_get(v___x_4484_, 1);
lean_dec(v_unused_4499_);
v___x_4490_ = v___x_4484_;
v_isShared_4491_ = v_isSharedCheck_4498_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_diag_4488_);
lean_inc(v_postponed_4487_);
lean_inc(v_zetaDeltaFVarIds_4486_);
lean_inc(v_mctx_4485_);
lean_dec(v___x_4484_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4498_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4493_; 
if (v_isShared_4491_ == 0)
{
lean_ctor_set(v___x_4490_, 1, v___x_4465_);
v___x_4493_ = v___x_4490_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_mctx_4485_);
lean_ctor_set(v_reuseFailAlloc_4497_, 1, v___x_4465_);
lean_ctor_set(v_reuseFailAlloc_4497_, 2, v_zetaDeltaFVarIds_4486_);
lean_ctor_set(v_reuseFailAlloc_4497_, 3, v_postponed_4487_);
lean_ctor_set(v_reuseFailAlloc_4497_, 4, v_diag_4488_);
v___x_4493_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4494_ = lean_st_ref_put(v___y_4464_, v___x_4493_);
v___x_4495_ = lean_box(0);
v___x_4496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4495_);
return v___x_4496_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_4503_, lean_object* v_isExporting_4504_, lean_object* v___x_4505_, lean_object* v___y_4506_, lean_object* v___x_4507_, lean_object* v_a_x3f_4508_, lean_object* v___y_4509_){
_start:
{
uint8_t v_isExporting_boxed_4510_; lean_object* v_res_4511_; 
v_isExporting_boxed_4510_ = lean_unbox(v_isExporting_4504_);
v_res_4511_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(v___y_4503_, v_isExporting_boxed_4510_, v___x_4505_, v___y_4506_, v___x_4507_, v_a_x3f_4508_);
lean_dec(v_a_x3f_4508_);
lean_dec(v___y_4506_);
lean_dec(v___y_4503_);
return v_res_4511_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4512_; 
v___x_4512_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4512_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; 
v___x_4513_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0);
v___x_4514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4514_, 0, v___x_4513_);
return v___x_4514_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4515_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1);
v___x_4516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4515_);
lean_ctor_set(v___x_4516_, 1, v___x_4515_);
return v___x_4516_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4517_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1);
v___x_4518_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
lean_ctor_set(v___x_4518_, 1, v___x_4517_);
lean_ctor_set(v___x_4518_, 2, v___x_4517_);
lean_ctor_set(v___x_4518_, 3, v___x_4517_);
lean_ctor_set(v___x_4518_, 4, v___x_4517_);
lean_ctor_set(v___x_4518_, 5, v___x_4517_);
return v___x_4518_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(lean_object* v_x_4519_, uint8_t v_isExporting_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_){
_start:
{
lean_object* v___x_4528_; lean_object* v_env_4529_; lean_object* v___x_4530_; uint8_t v_isModule_4531_; 
v___x_4528_ = lean_st_ref_get(v___y_4526_);
v_env_4529_ = lean_ctor_get(v___x_4528_, 0);
lean_inc_ref(v_env_4529_);
lean_dec(v___x_4528_);
v___x_4530_ = l_Lean_Environment_header(v_env_4529_);
v_isModule_4531_ = lean_ctor_get_uint8(v___x_4530_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4530_);
if (v_isModule_4531_ == 0)
{
lean_object* v___x_4532_; 
lean_dec_ref(v_env_4529_);
lean_inc(v___y_4526_);
lean_inc_ref(v___y_4525_);
lean_inc(v___y_4524_);
lean_inc_ref(v___y_4523_);
lean_inc(v___y_4522_);
lean_inc_ref(v___y_4521_);
v___x_4532_ = lean_apply_7(v_x_4519_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, lean_box(0));
return v___x_4532_;
}
else
{
uint8_t v_isExporting_4533_; 
v_isExporting_4533_ = lean_ctor_get_uint8(v_env_4529_, sizeof(void*)*8);
lean_dec_ref(v_env_4529_);
if (v_isExporting_4520_ == 0)
{
if (v_isExporting_4533_ == 0)
{
lean_object* v___x_4599_; 
lean_inc(v___y_4526_);
lean_inc_ref(v___y_4525_);
lean_inc(v___y_4524_);
lean_inc_ref(v___y_4523_);
lean_inc(v___y_4522_);
lean_inc_ref(v___y_4521_);
v___x_4599_ = lean_apply_7(v_x_4519_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, lean_box(0));
return v___x_4599_;
}
else
{
goto v___jp_4534_;
}
}
else
{
if (v_isExporting_4533_ == 0)
{
goto v___jp_4534_;
}
else
{
lean_object* v___x_4600_; 
lean_inc(v___y_4526_);
lean_inc_ref(v___y_4525_);
lean_inc(v___y_4524_);
lean_inc_ref(v___y_4523_);
lean_inc(v___y_4522_);
lean_inc_ref(v___y_4521_);
v___x_4600_ = lean_apply_7(v_x_4519_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, lean_box(0));
return v___x_4600_;
}
}
v___jp_4534_:
{
lean_object* v___x_4535_; lean_object* v_env_4536_; lean_object* v_nextMacroScope_4537_; lean_object* v_ngen_4538_; lean_object* v_auxDeclNGen_4539_; lean_object* v_traceState_4540_; lean_object* v_messages_4541_; lean_object* v_infoState_4542_; lean_object* v_snapshotTasks_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4597_; 
v___x_4535_ = lean_st_ref_take(v___y_4526_);
v_env_4536_ = lean_ctor_get(v___x_4535_, 0);
v_nextMacroScope_4537_ = lean_ctor_get(v___x_4535_, 1);
v_ngen_4538_ = lean_ctor_get(v___x_4535_, 2);
v_auxDeclNGen_4539_ = lean_ctor_get(v___x_4535_, 3);
v_traceState_4540_ = lean_ctor_get(v___x_4535_, 4);
v_messages_4541_ = lean_ctor_get(v___x_4535_, 6);
v_infoState_4542_ = lean_ctor_get(v___x_4535_, 7);
v_snapshotTasks_4543_ = lean_ctor_get(v___x_4535_, 8);
v_isSharedCheck_4597_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4597_ == 0)
{
lean_object* v_unused_4598_; 
v_unused_4598_ = lean_ctor_get(v___x_4535_, 5);
lean_dec(v_unused_4598_);
v___x_4545_ = v___x_4535_;
v_isShared_4546_ = v_isSharedCheck_4597_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_snapshotTasks_4543_);
lean_inc(v_infoState_4542_);
lean_inc(v_messages_4541_);
lean_inc(v_traceState_4540_);
lean_inc(v_auxDeclNGen_4539_);
lean_inc(v_ngen_4538_);
lean_inc(v_nextMacroScope_4537_);
lean_inc(v_env_4536_);
lean_dec(v___x_4535_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4597_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4550_; 
v___x_4547_ = l_Lean_Environment_setExporting(v_env_4536_, v_isExporting_4520_);
v___x_4548_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2);
if (v_isShared_4546_ == 0)
{
lean_ctor_set(v___x_4545_, 5, v___x_4548_);
lean_ctor_set(v___x_4545_, 0, v___x_4547_);
v___x_4550_ = v___x_4545_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v___x_4547_);
lean_ctor_set(v_reuseFailAlloc_4596_, 1, v_nextMacroScope_4537_);
lean_ctor_set(v_reuseFailAlloc_4596_, 2, v_ngen_4538_);
lean_ctor_set(v_reuseFailAlloc_4596_, 3, v_auxDeclNGen_4539_);
lean_ctor_set(v_reuseFailAlloc_4596_, 4, v_traceState_4540_);
lean_ctor_set(v_reuseFailAlloc_4596_, 5, v___x_4548_);
lean_ctor_set(v_reuseFailAlloc_4596_, 6, v_messages_4541_);
lean_ctor_set(v_reuseFailAlloc_4596_, 7, v_infoState_4542_);
lean_ctor_set(v_reuseFailAlloc_4596_, 8, v_snapshotTasks_4543_);
v___x_4550_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v_mctx_4553_; lean_object* v_zetaDeltaFVarIds_4554_; lean_object* v_postponed_4555_; lean_object* v_diag_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4594_; 
v___x_4551_ = lean_st_ref_put(v___y_4526_, v___x_4550_);
v___x_4552_ = lean_st_ref_take(v___y_4524_);
v_mctx_4553_ = lean_ctor_get(v___x_4552_, 0);
v_zetaDeltaFVarIds_4554_ = lean_ctor_get(v___x_4552_, 2);
v_postponed_4555_ = lean_ctor_get(v___x_4552_, 3);
v_diag_4556_ = lean_ctor_get(v___x_4552_, 4);
v_isSharedCheck_4594_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4594_ == 0)
{
lean_object* v_unused_4595_; 
v_unused_4595_ = lean_ctor_get(v___x_4552_, 1);
lean_dec(v_unused_4595_);
v___x_4558_ = v___x_4552_;
v_isShared_4559_ = v_isSharedCheck_4594_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_diag_4556_);
lean_inc(v_postponed_4555_);
lean_inc(v_zetaDeltaFVarIds_4554_);
lean_inc(v_mctx_4553_);
lean_dec(v___x_4552_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4594_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4560_; lean_object* v___x_4562_; 
v___x_4560_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__3);
if (v_isShared_4559_ == 0)
{
lean_ctor_set(v___x_4558_, 1, v___x_4560_);
v___x_4562_ = v___x_4558_;
goto v_reusejp_4561_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_mctx_4553_);
lean_ctor_set(v_reuseFailAlloc_4593_, 1, v___x_4560_);
lean_ctor_set(v_reuseFailAlloc_4593_, 2, v_zetaDeltaFVarIds_4554_);
lean_ctor_set(v_reuseFailAlloc_4593_, 3, v_postponed_4555_);
lean_ctor_set(v_reuseFailAlloc_4593_, 4, v_diag_4556_);
v___x_4562_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4561_;
}
v_reusejp_4561_:
{
lean_object* v___x_4563_; lean_object* v_r_4564_; 
v___x_4563_ = lean_st_ref_put(v___y_4524_, v___x_4562_);
lean_inc(v___y_4526_);
lean_inc_ref(v___y_4525_);
lean_inc(v___y_4524_);
lean_inc_ref(v___y_4523_);
lean_inc(v___y_4522_);
lean_inc_ref(v___y_4521_);
v_r_4564_ = lean_apply_7(v_x_4519_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, lean_box(0));
if (lean_obj_tag(v_r_4564_) == 0)
{
lean_object* v_a_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4581_; 
v_a_4565_ = lean_ctor_get(v_r_4564_, 0);
v_isSharedCheck_4581_ = !lean_is_exclusive(v_r_4564_);
if (v_isSharedCheck_4581_ == 0)
{
v___x_4567_ = v_r_4564_;
v_isShared_4568_ = v_isSharedCheck_4581_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_a_4565_);
lean_dec(v_r_4564_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4581_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v___x_4570_; 
lean_inc(v_a_4565_);
if (v_isShared_4568_ == 0)
{
lean_ctor_set_tag(v___x_4567_, 1);
v___x_4570_ = v___x_4567_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4580_; 
v_reuseFailAlloc_4580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4580_, 0, v_a_4565_);
v___x_4570_ = v_reuseFailAlloc_4580_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
lean_object* v___x_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
v___x_4571_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(v___y_4526_, v_isExporting_4533_, v___x_4548_, v___y_4524_, v___x_4560_, v___x_4570_);
lean_dec_ref(v___x_4570_);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4578_ == 0)
{
lean_object* v_unused_4579_; 
v_unused_4579_ = lean_ctor_get(v___x_4571_, 0);
lean_dec(v_unused_4579_);
v___x_4573_ = v___x_4571_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_dec(v___x_4571_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4576_; 
if (v_isShared_4574_ == 0)
{
lean_ctor_set(v___x_4573_, 0, v_a_4565_);
v___x_4576_ = v___x_4573_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4565_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
}
}
else
{
lean_object* v_a_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4591_; 
v_a_4582_ = lean_ctor_get(v_r_4564_, 0);
lean_inc(v_a_4582_);
lean_dec_ref_known(v_r_4564_, 1);
v___x_4583_ = lean_box(0);
v___x_4584_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(v___y_4526_, v_isExporting_4533_, v___x_4548_, v___y_4524_, v___x_4560_, v___x_4583_);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4584_);
if (v_isSharedCheck_4591_ == 0)
{
lean_object* v_unused_4592_; 
v_unused_4592_ = lean_ctor_get(v___x_4584_, 0);
lean_dec(v_unused_4592_);
v___x_4586_ = v___x_4584_;
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
else
{
lean_dec(v___x_4584_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v___x_4589_; 
if (v_isShared_4587_ == 0)
{
lean_ctor_set_tag(v___x_4586_, 1);
lean_ctor_set(v___x_4586_, 0, v_a_4582_);
v___x_4589_ = v___x_4586_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_a_4582_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___boxed(lean_object* v_x_4601_, lean_object* v_isExporting_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
uint8_t v_isExporting_boxed_4610_; lean_object* v_res_4611_; 
v_isExporting_boxed_4610_ = lean_unbox(v_isExporting_4602_);
v_res_4611_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(v_x_4601_, v_isExporting_boxed_4610_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
lean_dec(v___y_4606_);
lean_dec_ref(v___y_4605_);
lean_dec(v___y_4604_);
lean_dec_ref(v___y_4603_);
return v_res_4611_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(lean_object* v_x_4612_, uint8_t v_when_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_){
_start:
{
if (v_when_4613_ == 0)
{
lean_object* v___x_4621_; 
lean_inc(v___y_4619_);
lean_inc_ref(v___y_4618_);
lean_inc(v___y_4617_);
lean_inc_ref(v___y_4616_);
lean_inc(v___y_4615_);
lean_inc_ref(v___y_4614_);
v___x_4621_ = lean_apply_7(v_x_4612_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, lean_box(0));
return v___x_4621_;
}
else
{
uint8_t v___x_4622_; lean_object* v___x_4623_; 
v___x_4622_ = 0;
v___x_4623_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(v_x_4612_, v___x_4622_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_);
return v___x_4623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg___boxed(lean_object* v_x_4624_, lean_object* v_when_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_){
_start:
{
uint8_t v_when_boxed_4633_; lean_object* v_res_4634_; 
v_when_boxed_4633_ = lean_unbox(v_when_4625_);
v_res_4634_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(v_x_4624_, v_when_boxed_4633_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_);
lean_dec(v___y_4631_);
lean_dec_ref(v___y_4630_);
lean_dec(v___y_4629_);
lean_dec_ref(v___y_4628_);
lean_dec(v___y_4627_);
lean_dec_ref(v___y_4626_);
return v_res_4634_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___closed__2(void){
_start:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4637_ = ((lean_object*)(l_Lean_Meta_Sym_letToHave___closed__1));
v___x_4638_ = l_Lean_stringToMessageData(v___x_4637_);
return v___x_4638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave(lean_object* v_e_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_){
_start:
{
lean_object* v___f_4647_; lean_object* v___f_4648_; lean_object* v___y_4650_; lean_object* v___y_4651_; lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v___y_4654_; lean_object* v___y_4655_; uint8_t v___x_4664_; 
v___f_4647_ = ((lean_object*)(l_Lean_Meta_Sym_letToHave___closed__0));
lean_inc_ref(v_e_4639_);
v___f_4648_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_letToHave___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4648_, 0, v_e_4639_);
v___x_4664_ = l_Lean_Expr_hasLooseBVars(v_e_4639_);
lean_dec_ref(v_e_4639_);
if (v___x_4664_ == 0)
{
v___y_4650_ = v_a_4640_;
v___y_4651_ = v_a_4641_;
v___y_4652_ = v_a_4642_;
v___y_4653_ = v_a_4643_;
v___y_4654_ = v_a_4644_;
v___y_4655_ = v_a_4645_;
goto v___jp_4649_;
}
else
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v_a_4667_; lean_object* v___x_4669_; uint8_t v_isShared_4670_; uint8_t v_isSharedCheck_4674_; 
lean_dec_ref(v___f_4648_);
v___x_4665_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___closed__2, &l_Lean_Meta_Sym_letToHave___closed__2_once, _init_l_Lean_Meta_Sym_letToHave___closed__2);
v___x_4666_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(v___x_4665_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
v_a_4667_ = lean_ctor_get(v___x_4666_, 0);
v_isSharedCheck_4674_ = !lean_is_exclusive(v___x_4666_);
if (v_isSharedCheck_4674_ == 0)
{
v___x_4669_ = v___x_4666_;
v_isShared_4670_ = v_isSharedCheck_4674_;
goto v_resetjp_4668_;
}
else
{
lean_inc(v_a_4667_);
lean_dec(v___x_4666_);
v___x_4669_ = lean_box(0);
v_isShared_4670_ = v_isSharedCheck_4674_;
goto v_resetjp_4668_;
}
v_resetjp_4668_:
{
lean_object* v___x_4672_; 
if (v_isShared_4670_ == 0)
{
v___x_4672_ = v___x_4669_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v_a_4667_);
v___x_4672_ = v_reuseFailAlloc_4673_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
return v___x_4672_;
}
}
}
v___jp_4649_:
{
uint8_t v___x_4656_; lean_object* v___x_4657_; lean_object* v___f_4658_; uint8_t v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; uint8_t v___x_4662_; lean_object* v___x_4663_; 
v___x_4656_ = 0;
v___x_4657_ = lean_box(v___x_4656_);
v___f_4658_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_letToHave___lam__5___boxed), 10, 3);
lean_closure_set(v___f_4658_, 0, v___x_4657_);
lean_closure_set(v___f_4658_, 1, v___f_4647_);
lean_closure_set(v___f_4658_, 2, v___f_4648_);
v___x_4659_ = 0;
v___x_4660_ = lean_box(v___x_4659_);
v___x_4661_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___boxed), 10, 3);
lean_closure_set(v___x_4661_, 0, lean_box(0));
lean_closure_set(v___x_4661_, 1, v___f_4658_);
lean_closure_set(v___x_4661_, 2, v___x_4660_);
v___x_4662_ = 1;
v___x_4663_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(v___x_4661_, v___x_4662_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
return v___x_4663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___boxed(lean_object* v_e_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_){
_start:
{
lean_object* v_res_4683_; 
v_res_4683_ = l_Lean_Meta_Sym_letToHave(v_e_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_);
lean_dec(v_a_4681_);
lean_dec_ref(v_a_4680_);
lean_dec(v_a_4679_);
lean_dec_ref(v_a_4678_);
lean_dec(v_a_4677_);
lean_dec_ref(v_a_4676_);
return v_res_4683_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2(lean_object* v_00_u03b1_4684_, lean_object* v_x_4685_, uint8_t v_isExporting_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_){
_start:
{
lean_object* v___x_4694_; 
v___x_4694_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(v_x_4685_, v_isExporting_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_);
return v___x_4694_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___boxed(lean_object* v_00_u03b1_4695_, lean_object* v_x_4696_, lean_object* v_isExporting_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_){
_start:
{
uint8_t v_isExporting_boxed_4705_; lean_object* v_res_4706_; 
v_isExporting_boxed_4705_ = lean_unbox(v_isExporting_4697_);
v_res_4706_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2(v_00_u03b1_4695_, v_x_4696_, v_isExporting_boxed_4705_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_);
lean_dec(v___y_4703_);
lean_dec_ref(v___y_4702_);
lean_dec(v___y_4701_);
lean_dec_ref(v___y_4700_);
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2(lean_object* v_00_u03b1_4707_, lean_object* v_x_4708_, uint8_t v_when_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_){
_start:
{
lean_object* v___x_4717_; 
v___x_4717_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(v_x_4708_, v_when_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
return v___x_4717_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___boxed(lean_object* v_00_u03b1_4718_, lean_object* v_x_4719_, lean_object* v_when_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_){
_start:
{
uint8_t v_when_boxed_4728_; lean_object* v_res_4729_; 
v_when_boxed_4728_ = lean_unbox(v_when_4720_);
v_res_4729_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2(v_00_u03b1_4718_, v_x_4719_, v_when_boxed_4728_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_);
lean_dec(v___y_4726_);
lean_dec_ref(v___y_4725_);
lean_dec(v___y_4724_);
lean_dec_ref(v___y_4723_);
lean_dec(v___y_4722_);
lean_dec_ref(v___y_4721_);
return v_res_4729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3(lean_object* v_00_u03b1_4730_, lean_object* v_msg_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_){
_start:
{
lean_object* v___x_4739_; 
v___x_4739_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(v_msg_4731_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_);
return v___x_4739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___boxed(lean_object* v_00_u03b1_4740_, lean_object* v_msg_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_){
_start:
{
lean_object* v_res_4749_; 
v_res_4749_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3(v_00_u03b1_4740_, v_msg_4741_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_);
lean_dec(v___y_4747_);
lean_dec_ref(v___y_4746_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
return v_res_4749_;
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
